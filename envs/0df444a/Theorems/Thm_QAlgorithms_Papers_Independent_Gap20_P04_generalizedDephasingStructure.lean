-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P04_generalizedDephasingStructure
-- name    : QAlgorithms.Papers.Independent.Gap20.P04.generalizedDephasingStructure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:55:55.820307+00:00
-- url     : https://prove2.me/theorems/0f355f7f-a31b-423c-9403-0c330ed6fb7b
-- title:
--   generalized-dephasing-structure
-- statement:
--   Let $A'$ and $E$ be nonzero finite-dimensional registers, choose a preferred orthonormal input/receiver basis, and let $v_i\in E$ have norm one, without an orthogonality requirement. The map $U|i\rangle=|i\rangle|v_i\rangle$ is an isometry, and its receiver channel $\mathcal N$ is Hadamard. For complete dephasing $\Delta$ in that basis,
--   $$\mathcal N\circ\Delta=\Delta\circ\mathcal N=\Delta,\qquad
--   \mathcal N^c\circ\Delta=\mathcal N^c,$$
--   $$\mathcal N^c(\sigma)=\sum_i\langle i|\sigma|i\rangle\,|v_i\rangle\langle v_i|.$$
--   These identities explain why diagonal input marginals suffice in the subsequent CQ and CE optimizations.
-- source:
--   Trade-off capacities of the quantum Hadamard channels, arXiv:1001.1732v2, PDF p. 6, generalized-dephasing-structure

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

/-- PDF pp.5--6, (10): generalized dephasing is Hadamard and commutes with complete
 dephasing; the complement depends only on input diagonals. No orthogonality of v_i required. -/
theorem generalizedDephasingStructure (v : I → EuclideanSpace ℂ E)
    (hI : Nonempty I) (hv : ∀ i, ‖v i‖ = 1) :
    PhysicalDilation (gdDilation v) ∧ Hadamard (gdDilation v) ∧
    (∀ rho, receiverChannel (gdDilation v) (diagonal rho) = diagonal rho) ∧
    (∀ rho, diagonal (receiverChannel (gdDilation v) rho) = diagonal rho) ∧
    (∀ rho, complementaryChannel (gdDilation v) (diagonal rho) = complementaryChannel (gdDilation v) rho) ∧
    (∀ rho, complementaryChannel (gdDilation v) rho = ∑ i, rho i i • pureDensity (v i)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P04

end
