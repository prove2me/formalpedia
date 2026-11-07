-- Prove2me | Theorems.Thm_RGMISFast_proposition_4_1
-- name    : RGMISFast.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:47.727276+00:00
-- url     : https://prove2.me/theorems/05c031ee-b624-4e7e-83ac-8e729deff69b
-- title:
--   Proposition 4.1: size of admissible trees, $S_m(T_{a_m})\le 3L(a_0/a_m)^3256^m$
-- statement:
--   Let $G$ be a finite simple graph with all degrees at most $\Delta\ge2$, root $u^*$ and distinct ranks $r:V\to[0,\infty)$; let $h\ge0$, $L=h+8$, and suppose the ranks lie in $E_h$. Then every admissible tree $T$ satisfies, for $0\le m\le M$,
--   $$
--   S_m(T_{a_m})\le 3L\Big(\frac{a_0}{a_m}\Big)^3256^m, \tag{14}
--   $$
--   and in particular
--   $$
--   |V(T_{a_M})|\le 3L\Big(\frac{a_0}{a_M}\Big)^3256^M .
--   $$
--
--   Since $M=O(\log\Delta)$, this bounds the part of the tree with settling times at least $a_M$ by a polynomial in $\Delta$.
--
--   **Formalization Note** $T_{a_m}$ is the prefix of nodes $v$ with $a_m\le\tau(v)$; $M$ is defined from $\Delta$ by (6). Both clauses are stated.
--
--   Differences from the source:
--   - encoding: distinct ranks r : V → [0, ∞), the paper's standing assumption (§1.1, p.2; §2, p.10) → hypotheses `Function.Injective r` and `∀ v, 0 ≤ r v`; reason: the standing assumption written as hypotheses; it holds almost surely
--   - encoding: conditioned on E_h → for every rank vector satisfying `GoodEvent G Δ u (h + 8)`; reason: a deterministic statement on the event, as in the proof
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Proposition 4.1, eq. (14), p.15 (PDF p.17); proof in App. C, pp.30–32

import Mathlib
import Definitions.Def_RGMISFast_AdmissibleTree
import Definitions.Def_RGMISFast_GoodEvent

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Proposition 4.1 (Size of admissible trees; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.15, proof in App. C): conditioned on
`E_h`, every admissible tree `T` satisfies, for `0 ≤ m ≤ M`,
`S_m(T_{a_m}) ≤ 3L (a₀/a_m)^3 256^m` (14), and in particular
`|V(T_{a_M})| ≤ 3L (a₀/a_M)^3 256^M`.

**Formalization Note** `L = h + 8` with `h ≥ 0` (p.15); `E_h` is `GoodEvent G Δ u (h + 8)`;
`M = Mof Δ`. Ranks are distinct and nonnegative (standing assumption of §2), degrees are at most
`∆`, `∆ ≥ 2`. Both clauses are stated. -/
theorem proposition_4_1 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (h : ℝ)
    (hh : 0 ≤ h) (r : V → ℝ) (hinj : Function.Injective r) (hnn : ∀ v, 0 ≤ r v)
    (hE : GoodEvent G Δ u (h + 8) r) (T : AdmissibleTree G r u) :
    (∀ m : ℕ, m ≤ Mof Δ →
      Sm r (T.prefix (am m)) m ≤ 3 * (h + 8) * (a0 / am m) ^ 3 * 256 ^ m) ∧
    ((T.prefix (am (Mof Δ))).card : ℝ) ≤
      3 * (h + 8) * (a0 / am (Mof Δ)) ^ 3 * 256 ^ (Mof Δ) := by sorry

end RGMISFast
