-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_hadamardDegrading
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.hadamardDegrading
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:55:13.181002+00:00
-- url     : https://prove2.me/theorems/f78c6c4b-b0dc-492b-b990-3b097e974588
-- title:
--   Hadamard-degrading-map
-- statement:
--   Let $U:A'\to B\otimes E$ be a normalized finite-dimensional isometry with
--   $U_{(b,e),i}=\xi_b(e)\overline{\zeta_b(i)}$, where $\|\xi_b\|=1$. Let $\mathcal N$ and $\mathcal N^c$ be its receiver and complementary channels. Then for every matrix $\sigma$,
--   $$\mathcal N(\sigma)_{bc}=\langle\zeta_b|\sigma|\zeta_c\rangle\langle\xi_c|\xi_b\rangle.$$
--   Let $\mathcal M$ measure the orthonormal receiver basis and $\mathcal P$ prepare $|\xi_b\rangle\langle\xi_b|$ at outcome $b$. Their composition is an entanglement-breaking CPTP map with normalized Kraus operators $K_b=|\xi_b\rangle\langle b|$, and
--   $$\mathcal D=\mathcal P\circ\mathcal M,\qquad
--   \mathcal D\circ\mathcal N=\mathcal N^c.$$
--   This is the explicit factorized degrading construction for representation (8), not an identification of all degradable channels with Hadamard channels.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 5, Hadamard-degrading-map

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Claimed50.P24
  (Dilation PhysicalDilation ChannelEB Hadamard EqualMax AdditiveMax
   dephasingDilation dephasingGamma cloningDilation)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel dilationPower)

open QAlgorithms.Papers.Independent.Information100.P32 (diagonal)

open QAlgorithms.Papers.Independent.Dependency50.P24 (ensembleHolevoBits)

open QAlgorithms.Papers.Independent.Gap48.P44 (cqTimeSharing ceTimeSharing)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}

variable [Fintype I] [Fintype B] [Fintype E]

variable [Fintype J] [Fintype D] [Fintype F]

variable [DecidableEq I] [DecidableEq B] [DecidableEq E]

variable [DecidableEq J] [DecidableEq D] [DecidableEq F]

variable [Nonempty I] [Nonempty B] [Nonempty E]

variable [Nonempty J] [Nonempty D] [Nonempty F]

/-- PDF p.5, (8)--(9): explicit measurement-preparation degrading map for the given
rank-one complementary representation. Coefficients use <xi_c|xi_b>, fixing conjugation. -/
theorem hadamardDegrading (U : Dilation I B E) (hU : PhysicalDilation U)
    (xi : B → EuclideanSpace ℂ E) (hxi : ∀ b, ‖xi b‖ = 1)
    (zeta : B → EuclideanSpace ℂ I)
    (hrep : ∀ b e i, U (b,e) i = xi b e * conj (zeta b i)) :
    (∀ rho, receiverChannel U rho = hadamardCoefficient zeta xi rho) ∧
    IsKrausFamily (degradingKraus xi) ∧
    IsChannel (basisStatePreparation xi ∘ measureBasis) ∧
    ChannelEB (basisStatePreparation xi ∘ measureBasis) ∧
    (∀ rho, (basisStatePreparation xi ∘ measureBasis) rho = krausApply (degradingKraus xi) rho) ∧
    (∀ rho, (basisStatePreparation xi ∘ measureBasis) (receiverChannel U rho) = complementaryChannel U rho) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
