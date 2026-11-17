-- Prove2me | Theorems.Thm_PolyContract_Supplement_theorem_3_8
-- name    : PolyContract.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:01:46.816184+00:00
-- url     : https://prove2.me/theorems/3fd63b50-e177-4957-8748-6ba14f8565ff
-- title:
--   Theorem 3.8 — every subset is the unique minimizer of $\tilde f-\lambda_S a-\theta_S b$ for some $(\lambda_S,\theta_S)\in(0,1)^2$
-- statement:
--   This is the theorem of Allman, Lo, and McCormick, restated and proved in the paper.
--
--   For every $n\ge1$ and $E=[n]$ there are $a,b\in\mathbb R^E_{>0}$ and a submodular $\tilde f:2^E\to\mathbb R_{\ge0}$ with $\tilde f(\emptyset)=0$ such that every $S\subseteq E$ is the unique minimizer of
--   $$T\ \mapsto\ \tilde f(T)-\lambda_S\,a(T)-\theta_S\,b(T)$$
--   for some $(\lambda_S,\theta_S)\in(0,1)^2$.
--
--   Here $\tilde f$ is a directed cut function. After embedding into a polymatroid, every subset becomes a best-response level set, which forces exponentially many affine pieces of the best response.
--
--   Differences from the source:
--   - encoding: S is the unique minimizer → the value at S is strictly smaller than the value at every other subset T; reason: definition of a unique minimizer over the finite family of subsets
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem 3.8, p.9 (PDF p.10); proof App. B.5, p.26

import Mathlib
import Definitions.Def_PolyContract_IsRankFunction
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

set_option autoImplicit false

namespace PolyContract.Supplement

/-- **Theorem 3.8** (Allman, Lo, and McCormick [ALM22]; Klimm, Lippke, Warode, arXiv:2611.04934,
version of November 3, 2026, sha256 18cfc0a5…, p.9; proof App. B.5, p.26): for every `n ≥ 1` and
`E = [n]` there are `a, b ∈ ℝ^E_{>0}` and a submodular `f̃ : 2^E → ℝ_{≥0}` with `f̃(∅) = 0` such that
every `S ⊆ E` is the unique minimizer of `f̃ − λ_S a − θ_S b` for some `(λ_S, θ_S) ∈ (0, 1)²`.

**Formalization Note** `E = [n]` is `Fin n`; "unique minimizer" is: the value at `S` is strictly
smaller than the value at every other subset. -/
theorem theorem_3_8 (n : ℕ) (hn : 1 ≤ n) :
    ∃ (a b : Fin n → ℝ) (ft : Finset (Fin n) → ℝ),
      (∀ e, 0 < a e) ∧ (∀ e, 0 < b e) ∧ (∀ S, 0 ≤ ft S) ∧ NonmonotoneSubmod.Shared.Submodular ft ∧
        ft ∅ = 0 ∧
        ∀ S : Finset (Fin n), ∃ lam θ : ℝ, lam ∈ Set.Ioo (0 : ℝ) 1 ∧ θ ∈ Set.Ioo (0 : ℝ) 1 ∧
          ∀ T : Finset (Fin n), T ≠ S →
            ft S - lam * setSum a S - θ * setSum b S < ft T - lam * setSum a T - θ * setSum b T := by sorry

end PolyContract.Supplement
