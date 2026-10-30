-- Prove2me | Theorems.Thm_VehShare_SeqBounds_Bseq_antitone_workload
-- name    : VehShare.SeqBounds.Bseq_antitone_workload
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:53:44.769299+00:00
-- url     : https://prove2.me/theorems/41ef9419-5d66-4702-a850-b568b6cb4b6b
-- title:
--   Proof of Theorem 2: $B^K_i(q^s)\ge B^K_i$
-- statement:
--   Let $N\ge1$ and let $q^s$ be feasible for Problem (2). Write $B^j_i(W)$ for the sequence $B^j_0(W)=0$, $B^j_i(W)=j/(N+j-1+W(1-B^{j-1}_{i-1}(W)))$. Then
--
--   1. for all workloads $0\le W\le W'$ and all indices $j,i$, $B^j_i(W')\le B^j_i(W)$;
--   2. the workload $\lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q^s_{ij}/\mu_{ij}$ satisfies $0\le\lambda/\mu\le\Lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}/\mu_{ij}$;
--   3. consequently, for all $j,i$,
--   $$
--   B^j_i=B^j_i(\Lambda/\mu)\ \le\ B^j_i(\lambda/\mu)=B^j_i(q^s).
--   $$
--
--   Replacing every $q^s_{ij}$ by its largest value $1$ thus weakens each bound $B^K_i(q^s)$ to the instance-only bound $B^K_i$.
--
--   Differences from the source:
--   - reading: trip durations i.i.d. with a general distribution with rational Laplace transform and mean 1/μij, represented by a network of exponential stages (p. 4) → a phase-type law per pair: finitely many stages, entry probabilities β (total ≤ 1; the defect is a zero-length trip), rates r between stages, exit rates e, an exit reachable from every stage; 1/μij = β(−T)⁻¹𝟙; reason: the paper's state counts vehicles at each stage of the transit queue (footnote 1), so the model exists exactly for laws with such a stage network, i.e. phase-type laws; the general (not only Coxian) form is taken
--   - encoding: demand, prices, rewards and travel data on the pairs (i,j) ∈ 𝒜 (Λij > 0) → all of them given on every pair of locations; reason: pairs with Λij = 0 enter every rate, sum and constraint with factor 0; no instance changes
--   - encoding: prices pij with acceptance fractions qij = 1 − Fij(pij) (p. 5) → the fractions q ∈ [0,1] and the per-trip rewards Iij(q) as primitives, q·Iij(q) concave on [0,1]; reason: the paper reformulates the policy in terms of the quantiles q (p. 5); concavity of q·I is its only requirement
--   - generalization: q^s an optimal solution of Problem (2) with Δ ≥ K → q^s feasible for Problem (2) (bounds, balanced flows, workload ≤ Δ), any Δ; reason: the argument uses only that the flows of q^s are balanced and q^s ∈ [0,1]; the paper's optimal q^s is a special case
--   - encoding: Λ/μ with Λ = Σ_𝒜 Λij and 1/μ = Σ_𝒜 Λij/(Λ μij) (Theorem 1, p. 7) → LamOverMu = Σ_{i,j} Λij · meanTime ij; reason: equals Λ·(1/μ) when Λ > 0; when Λ = 0 the paper's 1/μ is 0/0 and the sum is 0
--   - generalization: B^K_i(q^s) ≥ B^K_i for i = 1, …, K → Bseq N W' j i ≤ Bseq N W j i for all 0 ≤ W ≤ W' and all indices j, i, with N ≥ 1; reason: specializes to the paper's claim at W = λ/μ ≤ W' = Λ/μ, j = K, 1 ≤ i ≤ K
--   - encoding: B^j_0 = 0 for j = 1, …, K → Bseq N W j 0 = 0 for every j (including B^0_0 = 0); reason: the paper's proof uses B^1_1 = 1/(N + Λ/μ), i.e. B^0_0 = 0
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, proof of Theorem 2, p. 10 (unnumbered display)

import Mathlib
import Definitions.Def_VehShare_SeqBounds_IsFeasible2
import Definitions.Def_VehShare_SeqBounds_LamOverMu
import Definitions.Def_VehShare_SeqBounds_Bseq

namespace VehShare.SeqBounds

/-- **`B^K_i(q^s) ≥ B^K_i`: the bounds decrease in the workload.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), proof of Theorem 2, p. 10 (unnumbered display: "By substituting `q^s_ij` for all
`(i,j)` in `𝒜` with their largest values 1 and using the notation `B^K_i = B^K_i(𝟏)` ... Hence,
`α(K) ≥ B^K_i(q^s) ≥ B^K_i` for all `i = 1, 2, ···, K`").

Let `N ≥ 1` and let `q^s` be feasible for Problem (2). Then
1. for all workloads `0 ≤ W ≤ W'` and all indices `j, i`, `Bseq N W' j i ≤ Bseq N W j i`;
2. `0 ≤ λ/μ ≤ Λ/μ`, where `λ/μ` is the workload of `q^s`;
3. for all `j, i`, `B^j_i = Bseq N (Λ/μ) j i ≤ Bseq N (λ/μ) j i = B^j_i(q^s)`.

**Formalization Note.** Clauses 1 and 3 hold for all indices, not only the paper's `1 ≤ i ≤ K`
(a generalization; Reading 9). Only feasibility of `q^s` is used, with any `Δ`. -/
theorem Bseq_antitone_workload (P : Instance) (Δ : ℝ) (qs : P.L → P.L → ℝ)
    (hqs : IsFeasible2 P Δ qs) (N : ℕ) (hN : 1 ≤ N) :
    (∀ W W' : ℝ, 0 ≤ W → W ≤ W' → ∀ j i : ℕ, Bseq N W' j i ≤ Bseq N W j i) ∧
      (0 ≤ workload P qs ∧ workload P qs ≤ LamOverMu P) ∧
      ∀ j i : ℕ, Bseq N (LamOverMu P) j i ≤ Bseq N (workload P qs) j i := by sorry

end VehShare.SeqBounds
