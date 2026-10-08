-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Supermod_closed_form
-- name    : ReliableFacilityLoc.Supermod.closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:58.199972+00:00
-- url     : https://prove2.me/theorems/fe9d1c87-2a8d-4613-9c02-bf4a9fed12a6
-- title:
--   A.3 / §3.3.1: closed form $\Phi_i(S) = \lambda_i\sum_{k=1}^{\bar n+1} C_k + \sum_{j\in S}\mu_{ij}$
-- statement:
--   Assume $\lambda_i \ge 0$, $0 \le q_j < 1$ for every regular facility and $R \ge 1$. Let $S$ be a set of regular facilities with $|S| \le R$, listed as $j_1, \dots, j_n$ in nondecreasing order of distance $d_{ij}$ (ties in any order), and let $\bar n$, $P_k$, $C_k$ be as in the proof of Proposition 3. Then
--
--   $$
--   \Phi_i(S) = \lambda_i \sum_{k=1}^{\bar n} P_{k-1}(1-q_{j_k})\, d_{ij_k} + \lambda_i P_{\bar n}\varphi_i + \sum_{j\in S}\mu_{ij} = \lambda_i \sum_{k=1}^{\bar n+1} C_k + \sum_{j\in S}\mu_{ij}.
--   $$
--
--   In words: it is optimal to assign the facilities of $S$ level by level in increasing order of distance, as long as the distance does not exceed the penalty $\varphi_i$, and then the emergency facility. This closed form turns the mixed-integer program defining $\Phi_i(S)$ into an explicit expression, on which the supermodularity argument operates.
--
--   **Formalization Note** The hypothesis $|S| \le R$ is the cardinality constraint (6c) of (MSF$_i$); without it the formula fails, because only $R$ regular facilities fit at the levels $0, \dots, R-1$. No sign is assumed on $d$, $\varphi_i$ or $\mu$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 36 (PDF 38), Appendix A.3, first display; also §3.3.1, p. 13 (PDF 15)

import Mathlib
import Definitions.Def_ReliableFacilityLoc_Supermod_RSP
import Definitions.Def_ReliableFacilityLoc_Supermod_ClosedForm

open Finset

namespace ReliableFacilityLoc.Supermod

/-- **Closed form of `Φ_i(S)`** (Cui, Ouyang & Shen, UCTC-FR-2010-02 (Feb. 2010), §3.3.1, p. 13,
PDF 15, and Appendix A.3, p. 36, PDF 38, the first display). Let `S` be a set of at most `R`
regular facilities and `L = [j_1, …, j_n]` a list of the elements of `S` in nondecreasing order of
distance `d_ij`. Then
`Φ_i(S) = λ_i Σ_{k=1}^{n̄} P_{k−1}(1 − q_{j_k}) d_{ij_k} + P_{n̄} φ_i + Σ_{j∈S} µ_ij
        = λ_i Σ_{k=1}^{n̄+1} C_k + Σ_{j∈S} µ_ij`,
where `n̄` is the number of elements of `S` with `d_ij ≤ φ_i`.

Printed (p. 36): "Following a similar argument as in the proof of Proposition 2, we know that it is
optimal to assign the facilities level by level in increasing order of distance, until the
transportation cost exceeds the penalty cost, i.e., Φi(S) = λi Σ_{k=1}^{n̄} Pk−1(1 − qjk)dijk + Pn̄φi
+ Σ_{j∈S} µij = λi Σ_{k=1}^{n̄+1} Ck + Σ_{j∈S} µij."

Formalization Note: the hypothesis `S.card ≤ R` is not printed next to the display; it is the
constraint (6c) of (MSF_i) (p. 13), and without it the formula is false (only `R` regular
facilities fit at the levels `0, …, R − 1`). `0 ≤ λ_i` (a demand rate), `0 ≤ q_j < 1` and
`R ≥ 1` are the standing assumptions of §3.1 (pp. 7–8). Ties in distance are allowed: the
statement holds for every list of `S` sorted by distance. No sign is assumed on `d`, `φ_i`, `µ`. -/
theorem closed_form {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R)
    (S : Finset (Fin J)) (hS : S.card ≤ R) (L : List (Fin J)) (hLnd : L.Nodup)
    (hLS : L.toFinset = S) (hLsort : L.Pairwise (fun a b => d a ≤ d b)) :
    Phi lam d phi q mu R S =
      lam * ∑ k ∈ Icc 1 (countLE d phi L + 1), Ck d phi q L k + ∑ j ∈ S, mu j := by sorry

end ReliableFacilityLoc.Supermod
