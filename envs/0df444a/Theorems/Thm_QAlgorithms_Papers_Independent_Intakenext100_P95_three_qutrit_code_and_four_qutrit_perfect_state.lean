-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P95_three_qutrit_code_and_four_qutrit_perfect_state
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P95.three_qutrit_code_and_four_qutrit_perfect_state
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:48:25.402191+00:00
-- url     : https://prove2.me/theorems/2c9a36a2-ec81-40bc-a588-bfe65d075f05
-- title:
--   The explicit qutrit erasure code and self-dual CSS perfect state
-- statement:
--   Use arithmetic modulo three. Define the encoder by
--
--   $$M\lvert l\rangle=\frac1{\sqrt3}\sum_{a\in\mathbb Z_3}\lvert a,a+l,a+2l\rangle,$$
--
--   and define the four-qutrit state, with reference leg last, by
--
--   $$\lvert\Psi\rangle=\frac13\sum_{a,l\in\mathbb Z_3}\lvert a,a+l,a+2l,l\rangle.$$
--
--   The encoder is isometric, and erasure of any set of at most one physical qutrit is correctable by a CPTP recovery channel. The displayed state is normalized and perfect; every marginal on at most two qutrits is maximally mixed. It spans the joint $+1$ space of the X-type and Z-type checks with the same rows $(1,1,1,0)$ and $(1,-1,0,1)$, so this state is self-dual CSS. Here $X\lvert j\rangle=\lvert j-1\rangle$ and $Z\lvert j\rangle=\omega^j\lvert j\rangle$ with $\omega=e^{2\pi i/3}$. The construction supplies the source’s concrete qutrit example.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, PDF p. 45, Appendix A.2: explicit three-qutrit erasure code and four-qutrit perfect state

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF pp.45–46, Appendix A.2: the explicit three-qutrit erasure code and
normalized four-qutrit perfect state. Recovery channels precede the input operator.
The shared X/Z check rows and the one-dimensional +1 space state the self-dual CSS clause. -/
theorem three_qutrit_code_and_four_qutrit_perfect_state :
    qutritEncoderᴴ * qutritEncoder = 1 ∧
    (∀ A : Finset (Fin 3), A.card ≤ 1 →
      ∃ R : Superop (SubsetConfig Trit Aᶜ) Trit, IsChannel R ∧
        ∀ rho : Matrix Trit Trit ℂ,
          R (subsetDensity Aᶜ (qutritEncoder * rho * qutritEncoderᴴ)) = rho) ∧
    IsState fourQutritState ∧ IsPerfect fourQutritState ∧
    (∀ A : Finset (Fin 4), A.card ≤ 2 →
      subsetDensity A (pureDensity fourQutritState) = ((Fintype.card (SubsetConfig Trit A) : ℂ)⁻¹ • 1)) ∧
    qutritCSSSpace = Submodule.span ℂ {fourQutritState} := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P95
