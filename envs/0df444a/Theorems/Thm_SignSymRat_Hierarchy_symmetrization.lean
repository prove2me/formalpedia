-- Prove2me | Theorems.Thm_SignSymRat_Hierarchy_symmetrization
-- name    : SignSymRat.Hierarchy.symmetrization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:42.934023+00:00
-- url     : https://prove2.me/theorems/3f4ebbdd-f770-4baa-85c3-cbc3599d3d24
-- title:
--   Proof of Theorem 4.3 — cancellation and symmetric support
-- statement:
--   For a finite exponent set $A$, let $R(A)$ be its parity sign-symmetry group and $\bar A$ its closure. Each monomial outside $\bar A$ cancels under the group action, and the average of any real polynomial has support in $\bar A$:
--
--   $$\alpha\notin\bar A\implies\sum_{r\in R(A)}\theta_r(x^\alpha)=0,\qquad
--   \frac{1}{|R(A)|}\sum_{r\in R(A)}\theta_r(h)\in\mathbb R[\bar A].$$
--
--   This is the support restriction used in the sign-symmetric dual (SD).
--
--   **Formalization Note** The general finite set $A$ specializes to each $A_i$ in the paper. `ZMod 2` supplies the parity pairing; no source assumption about the rational functions is needed for this algebraic claim.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 11, proof of Theorem 4.3, symmetrization passage

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_SignSym

open MvPolynomial

namespace SignSymRat.Hierarchy

/-- The monomial cancellation and support claim in the proof of Theorem 4.3, p. 11. -/
theorem symmetrization {n : ℕ} (A : Finset (Fin n →₀ ℕ)) :
    (∀ α : Fin n →₀ ℕ, α ∉ symClosure A →
      (∑ r ∈ signSym A, theta r (monomial α (1 : ℝ))) = 0) ∧
    (∀ h : MvPolynomial (Fin n) ℝ, SupportedIn (symClosure A) (symAvg A h)) := by sorry

end SignSymRat.Hierarchy
