-- Prove2me | Theorems.Thm_ProbMFG_Existence_lemma_3_10
-- name    : ProbMFG.Existence.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:46.658206+00:00
-- url     : https://prove2.me/theorems/3baebfc7-0024-4efe-9cbc-0462af055d12
-- title:
--   Lemma 3.10 — bounded-gradient approximations under strong convexity
-- statement:
--   Assume (A.1)–(A.7) and the strengthened state and control convexity condition (3.28) with $\gamma>0$. Then there are positive constants $\lambda',c'_L$, depending only on $\lambda,c_L,\gamma$, and sequences of costs $(f^n,g^n)$ such that each pair satisfies (A.1)–(A.7) with these common parameters, each pair has bounded spatial gradients, and each pair eventually agrees exactly with $(f,g)$ on any prescribed bounded subset.
--   $$\forall R<\infty\;\exists n_0\;\forall n\ge n_0:\quad (f^n,g^n)=(f,g)\text{ on the radius-}R\text{ domain.}$$
--   These approximations bridge Proposition 3.8 and Lemma 3.9.
--
--   **Formalization Note** The gradient bound may depend on $n$. The constants $\lambda',c'_L$ occur before the model data in the Lean quantifiers.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2723, Lemma 3.10 and (3.28); https://doi.org/10.1137/120883499

import Mathlib
import Definitions.Def_ProbMFG_Existence_Model

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMFG.Existence

/-- Lemma 3.10: bounded-gradient approximations under (3.28). The new
convexity and regularity constants depend only on λ, c_L, and γ. -/
theorem lemma_3_10 (lam cL γ : ℝ) (hlam : 0 < lam) (hcL : 0 < cL) (hγ : 0 < γ) :
    ∃ lam' cL' : ℝ, 0 < lam' ∧ 0 < cL' ∧
      ∀ {d m k : ℕ} (M : Model d m k),
        M.Assumptions lam cL → M.StronglyConvexX lam γ →
        ∃ (fn : ℕ → ℝ≥0 → State d → Measure (State d) → Action k → ℝ)
          (gn : ℕ → State d → Measure (State d) → ℝ),
          (∀ n : ℕ, 1 ≤ n →
            ({ M with f := fn n, g := gn n } : Model d m k).Assumptions lam' cL' ∧
            ∃ B : ℝ, 0 ≤ B ∧ ∀ t ≤ M.T, ∀ x μ a, IsP2 μ →
              ‖({ M with f := fn n, g := gn n } : Model d m k).dfx t x μ a‖ ≤ B ∧
              ‖({ M with f := fn n, g := gn n } : Model d m k).dgx x μ‖ ≤ B) ∧
          (∀ R : ℝ, 0 ≤ R → ∃ n₀ : ℕ, ∀ n ≥ n₀,
            ∀ t ≤ M.T, ∀ x μ a, IsP2 μ → ‖x‖ ≤ R → ‖a‖ ≤ R →
              (moment 2 μ).toReal ≤ R →
                fn n t x μ a = M.f t x μ a ∧ gn n x μ = M.g x μ) := by sorry

end ProbMFG.Existence
