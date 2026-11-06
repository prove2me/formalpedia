-- Prove2me | Theorems.Thm_ReserveLB_lemma_6_1
-- name    : ReserveLB.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:00.787499+00:00
-- url     : https://prove2.me/theorems/db444c8a-9cd7-4cff-b30d-3bb968641c73
-- title:
--   Lemma 6.1 — repeated-pool bound: density below $e^2\beta + 1/8$, whole-job cost below $e^2\beta + 9/8$
-- statement:
--   Let the pools $p$ have distinct power-of-two endpoint counts $R_p = 2^{e_p}$. Original $j$ has a normalized portion $Z_{jp} \in [0,1]$ in each pool, at most one of them positive (portions are exclusive across pools), and
--   $$
--   \sum_j \mathbb E Z_{jp} \le \beta R_p\quad\text{for every pool } p,\qquad \beta \ge 1 .
--   $$
--   In every pool, original $j$ has two independent uniform endpoints $U^1_{jp}, U^2_{jp}$ of that pool, independent of its portions, and the data of different originals are independent; the portions of one original need not be independent of each other. Then the global density $D$ (the largest ratio of trapped work to the number of endpoints, over nonempty endpoint sets) and the whole-job cost $C$ (the least maximum endpoint load when every portion goes to one of its two endpoints) satisfy
--   $$
--   \mathbb E D < e^2\beta + \tfrac18,\qquad \mathbb E C < e^2\beta + \tfrac98 .
--   $$
--
--   This bounds the repeated-class work of the construction; it enters the table (16) through the repeated pools.
--
--   Differences from the source:
--   - reading: two independent uniform endpoints per original; pair samples are independent across originals and of sizes → for each original and pool, two independent uniform endpoints of that pool, jointly independent of the original's portions; the triples (portions, endpoints, endpoints) independent across originals; no independence across pools or portions of one original; reason: the preceding paragraph of p.11; the proof is per pool and unions across pools
--   - encoding: portions exclusive across disjoint pools; normalized processing times; global density; additive whole-job cost → at most one nonzero portion per original; unit-speed endpoints (pool, index); poolDensity (max over nonempty endpoint sets); poolCost (min over endpoint choices of the max load); reason: same instances
--   - encoding: random portions in [0, 1], uniform endpoints → measurable maps, 0 ≤ Z ω ≤ 1 for every ω, P{U = a} = 1/R_p for every endpoint a; reason: as for (2); same instances
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 6.1 and the preceding paragraph, p.11

import Mathlib
import Definitions.Def_ReserveLB_poolDensity
import Definitions.Def_ReserveLB_poolCost

open MeasureTheory ProbabilityTheory

namespace ReserveLB

/-- **Lemma 6.1 — repeated-pool bound.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 6.1, p.11: "Suppose independent original [0, 1] portions, exclusive across disjoint
pools of distinct power-of-two counts R, have total mean at most βR in each pool, β ≥ 1. Two
independent uniform endpoints per original give expected global density below e²β + 1/8, and
additive whole-job cost below e²β + 9/8." Context, p.11: "Pool portions denote normalized
processing times. Pair samples are independent across originals and of sizes; different portions
of one original need not be independent."

Pools `p` have distinct power-of-two endpoint counts `R_p = 2^(e_p)`. Original `j` has a portion
`Z_jp ∈ [0, 1]` in each pool, at most one of them nonzero, with `Σ_j E Z_jp ≤ β R_p` for every pool
and `β ≥ 1`. In every pool, original `j` draws two independent uniform endpoints `U1_jp`, `U2_jp`,
independent of its portions; the data of different originals are independent. Then the expected
global density is below `e²β + 1/8` and the expected whole-job cost is below `e²β + 9/8`.

**Formalization Note.** No independence is assumed between the portions of one original, nor
between the endpoint pairs of one original in different pools. "Exclusive" is "at most one positive
portion per original". Density and cost are `poolDensity` and `poolCost`. -/
theorem lemma_6_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {Pl : Type*} [Fintype Pl] [DecidableEq Pl] (e : Pl → ℕ) (he : Function.Injective e)
    (Z : Fin n → Pl → Ω → ℝ) (hZm : ∀ j p, Measurable (Z j p))
    (hZ01 : ∀ j p ω, 0 ≤ Z j p ω ∧ Z j p ω ≤ 1)
    (hexcl : ∀ j p p' ω, p ≠ p' → Z j p ω = 0 ∨ Z j p' ω = 0)
    (β : ℝ) (hβ : 1 ≤ β) (hmean : ∀ p, ∑ j, ∫ ω, Z j p ω ∂P ≤ β * 2 ^ e p)
    (U1 U2 : Fin n → (p : Pl) → Ω → Fin (2 ^ e p))
    (hU1m : ∀ j p, Measurable (U1 j p)) (hU2m : ∀ j p, Measurable (U2 j p))
    (hU1 : ∀ j p a, P.real {ω | U1 j p ω = a} = 1 / 2 ^ e p)
    (hU2 : ∀ j p a, P.real {ω | U2 j p ω = a} = 1 / 2 ^ e p)
    (hpair : ∀ j p, IndepFun (U1 j p) (U2 j p) P)
    (hsep : ∀ j, IndepFun (fun ω p => Z j p ω) (fun ω => ((fun p => U1 j p ω), (fun p => U2 j p ω))) P)
    (hind : iIndepFun (fun j ω => ((fun p => Z j p ω), (fun p => U1 j p ω), (fun p => U2 j p ω))) P) :
    ∫ ω, poolDensity (fun p => 2 ^ e p) (fun j p => Z j p ω) (fun j p => U1 j p ω)
        (fun j p => U2 j p ω) ∂P < Real.exp 2 * β + 1 / 8 ∧
    ∫ ω, poolCost (fun p => 2 ^ e p) (fun j p => Z j p ω) (fun j p => U1 j p ω)
        (fun j p => U2 j p ω) ∂P < Real.exp 2 * β + 9 / 8 := by sorry

end ReserveLB
