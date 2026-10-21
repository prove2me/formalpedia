-- Prove2me | Theorems.Thm_ProcFlex_DMGI_theorem_2a
-- name    : ProcFlex.DMGI.theorem_2a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:26.865794+00:00
-- url     : https://prove2.me/theorems/c054cfee-4e45-40e4-b840-f3f429402019
-- title:
--   Theorem 2(a): DMGI dominance implies robust dominance
-- statement:
--   Fix a robust measure $R^f$ from the paper's class and a nonempty compact nonnegative uncertainty set $U$ that is part-wise independently symmetric around $\mu$. If two designs satisfy $\delta^K_\mu(A_1)\ge\delta^K_\mu(A_2)$ for every feasible $K\in Q$, then
--
--   $$
--   R^f(A_1,U)\ge R^f(A_2,U).
--   $$
--
--   This is the sufficient comparison criterion used to turn the alternate chain's DMGI bounds into worst-case-score bounds.
--
--   **Formalization Note** The same perturbation centre $\mu$ is used by both designs, and the deterministic score is continuous in nonnegative demand for both.
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), p. 18, Theorem 2(a)

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model

namespace ProcFlex.DMGI

/-- Theorem 2(a), p. 18: DMGI dominance implies dominance of any robust
measure in Γ for the same fixed perturbation centre. -/
theorem theorem_2a {m n T : ℕ} (S : System m n T) (hS : S.IsValid)
    (A₁ A₂ : Design m n) (h : ℝ → (Fin T → ℝ) → ℝ)
    (hh : ∀ y, StrictMono (fun x => h x y))
    (hcont₁ : ContinuousOn (f S h A₁) {d | ∀ i, 0 ≤ d i})
    (hcont₂ : ContinuousOn (f S h A₂) {d | ∀ i, 0 ≤ d i})
    (U : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (hU : IsSymmetricAround S U μ)
    (hUpos : ∀ d ∈ U, ∀ i, 0 ≤ d i)
    (hUne : U.Nonempty) (hUc : IsCompact U)
    (hδ : ∀ K, InQ S K → dmgi S μ K A₂ ≤ dmgi S μ K A₁) :
    Rf S h A₂ U ≤ Rf S h A₁ U := by sorry

end ProcFlex.DMGI
