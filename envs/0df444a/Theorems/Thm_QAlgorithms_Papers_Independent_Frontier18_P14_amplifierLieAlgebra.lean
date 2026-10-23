-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_amplifierLieAlgebra
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.amplifierLieAlgebra
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:08:35.451799+00:00
-- url     : https://prove2.me/theorems/fa8b8afb-25f8-46d2-bb4e-cc4843025a4a
-- title:
--   Amplifier Lie algebra and hyperbolic Casimir
-- statement:
--   On the two-mode finite-occupation invariant core, define $K_t=(a_1^\dagger a_1+a_2a_2^\dagger)/2$, $K_x=(a_1a_2+a_1^\dagger a_2^\dagger)/2$, $K_y=i(a_1a_2-a_1^\dagger a_2^\dagger)/2$, and $K_z=(a_1^\dagger a_1-a_2a_2^\dagger)/2$. Then
--
--   $$[K_x,K_y]=-iK_t,\quad[K_y,K_t]=iK_x,\quad[K_t,K_x]=iK_y,\qquad K_t^2-K_x^2-K_y^2=K_z(K_z+I).$$
--
--   The operator $K_z$ commutes with $K_t,K_x,K_y$. Moreover $K_t=L_t+I/2$ and $K_z=L_z-I/2$. These identities supply the amplifier's hyperbolic Lie algebra with its vacuum shifts retained.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 30, §6.2: amplifier Lie algebra and hyperbolic Casimir

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF p.30, (6.10)–(6.12): hyperbolic commutators and Casimir on the
common invariant core. The vacuum shifts a2 a2† are kept literally in Kt,Kz. -/
theorem amplifierLieAlgebra :
    commutator lorentzX lorentzY = -Complex.I • lorentzT ∧
    commutator lorentzY lorentzT = Complex.I • lorentzX ∧
    commutator lorentzT lorentzX = Complex.I • lorentzY ∧
    commutator lorentzZ lorentzT = 0 ∧
    commutator lorentzZ lorentzX = 0 ∧
    commutator lorentzZ lorentzY = 0 ∧
    lorentzT = stokesT + (1 / 2 : ℂ) • (1 : Module.End ℂ (Core 2)) ∧
    lorentzZ = stokesZ - (1 / 2 : ℂ) • (1 : Module.End ℂ (Core 2)) ∧
    lorentzT ^ 2 - lorentzX ^ 2 - lorentzY ^ 2 = lorentzZ * (lorentzZ + 1) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
