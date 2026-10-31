-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_linearAngleSolvability
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.linearAngleSolvability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:53:58.398207+00:00
-- url     : https://prove2.me/theorems/d11f6c0f-8b0b-45f3-9030-9a5bd47f276b
-- title:
--   Real column-span and nonsingular angle-system criteria
-- statement:
--   Let $n\ge1$, and consider $m$ tensor monomials built from $I,Z/2,(X+iY)/2,(X-iY)/2$, with complex coefficients $c_\lambda$. Let $P_{\lambda\ell}\in\{0,+1,-1\}$ be their real order matrix. For any independent sign choice $s_\lambda\in\{+1,-1\}$, if $\pi s$ lies in the real column span of $P$, then there are real angles with
--
--   $$P\boldsymbol\phi=\pi s,\qquad K_z(\boldsymbol\phi)\Bigl(\sum_\lambda c_\lambda T_\lambda\Bigr)K_z(\boldsymbol\phi)^\dagger=-\sum_\lambda c_\lambda T_\lambda.$$
--
--   In particular, if $m=n$ and $\det P\ne0$, such angles exist for every sign choice. This is a sufficient real linear-system test; no converse restricts the integer congruence lifts to these particular right-hand sides.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 8, (40): column-span test and nonsingular square case

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- (40), PDF p.8: the real column-span test is sufficient; the nonsingular
square case solves each independent choice of signs. It is not asserted
that restricting all congruence lifts to plus or minus pi is necessary. -/
theorem linearAngleSolvability {n : ℕ} (hn : 0 < n) :
    (∀ (m : ℕ) (nu : Fin m → Fin n → Fin 4) (c : Fin m → ℂ)
      (signs : Fin m → Bool),
      (fun a => if signs a then Real.pi else -Real.pi) ∈
        Set.range (orderMatrix nu).mulVec →
      ∃ phi : Fin n → ℝ,
        (orderMatrix nu).mulVec phi = (fun a => if signs a then Real.pi else -Real.pi) ∧
        adjointConjugation (individualZRotation phi) (tensorOperatorSum nu c) = -tensorOperatorSum nu c) ∧
    (∀ (nu : Fin n → Fin n → Fin 4) (c : Fin n → ℂ),
      (orderMatrix nu).det ≠ 0 → ∀ signs : Fin n → Bool,
      ∃ phi : Fin n → ℝ,
        (orderMatrix nu).mulVec phi = (fun a => if signs a then Real.pi else -Real.pi) ∧
        adjointConjugation (individualZRotation phi) (tensorOperatorSum nu c) = -tensorOperatorSum nu c) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
