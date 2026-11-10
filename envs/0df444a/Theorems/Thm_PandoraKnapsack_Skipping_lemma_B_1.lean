-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_lemma_B_1
-- name    : PandoraKnapsack.Skipping.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:25:40.155651+00:00
-- url     : https://prove2.me/theorems/a68db2d7-0654-4bb5-8abc-d8cb78d09632
-- title:
--   Lemma B.1 — the compact LP keeps a quarter of the time-indexed LP value
-- statement:
--   Let $I$ be a valid MPK instance with capacity $T$ and let $b\in\mathbb N$. Then $\Psi_P(b)\ge\frac14\Psi(b)$: for every feasible solution $x$ of $\Psi(b)$ there is a feasible solution $\hat x$ of $\Psi_P(b)$ with
--   $$\tfrac14\sum_{i,j}\sum_{t=0}^{b}w_{i,j,t}\,x_{i,j,t}\ \le\ \sum_{i,j}\sum_{\tau\in T_b}w_{i,j,2\tau}\,\hat x_{i,j,\tau}.$$
--
--   Differences from the source:
--   - encoding: Ψ_P(b) ≥ ¼ Ψ(b), an inequality between two optimal values → every feasible x of Ψ(b) has a feasible x̂ of Ψ_P(b) with objective_P(x̂) ≥ objective(x)/4; reason: both maxima are attained (nonempty compact polytopes), so the statements are equivalent; no real supremum is taken
--   - generalization: b with T_b = {0} ∪ {2^l : l ≤ ⌊log b⌋}, undefined at b = 0 → every b ∈ ℕ, with T_0 = {0}; reason: for b ≥ 1 the breakpoint set is the source's; b = 0 is an added case where Ψ_P(0) and Ψ(0) coincide
--   - encoding: LP variables x_{i,j,t} for t ∈ {0,…,b} → arrays Fin n → Fin m → ℕ → ℝ whose coordinates outside the index set are ignored; reason: same feasible points and objective values on the index set
--   - encoding: items [n] and choices [m] indexed from 1 → Fin n and Fin m, indexed from 0; reason: index shift; same instances
--   - reading: item-choice costs p_i^j paid up front (sign not stated) → 0 ≤ p_i^j in IsValid; reason: §2 calls p_i^j a cost incurred up front and Definition 2.1 divides by it; a negative cost would reward overflow, which the model never does
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, Lemma B.1, printed p. 40 (PDF 42)

import Definitions.Def_PandoraKnapsack_Skipping_CompactLP

namespace PandoraKnapsack.Skipping

/-- **Lemma B.1** (Barak et al. 2026, *Pandora's Knapsack via Simple Policies*, supplied PDF,
SHA256 45e5830b…7a2d, printed p. 40, PDF 42). `Ψ_P(b) ≥ ¼ Ψ(b)`.

**Formalization Note.** Both maxima are attained, so the inequality is stated as: every feasible
solution `x` of `Ψ(b)` has a feasible solution `x̂` of `Ψ_P(b)` with objective at least a quarter
of that of `x`. Every `b ∈ ℕ` is allowed; for `b = 0` the breakpoint set is `{0}`. -/
theorem lemma_B_1 {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (b : ℕ) (x : LPArray n m)
    (hx : PsiFeasible I b x) :
    ∃ xHat : LPArray n m, PsiPFeasible I b xHat ∧
      psiObjective I b x / 4 ≤ psiPObjective I b xHat := by sorry

end PandoraKnapsack.Skipping
