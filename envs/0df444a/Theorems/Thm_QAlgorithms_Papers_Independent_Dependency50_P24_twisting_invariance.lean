-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_twisting_invariance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.twisting_invariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:09:00.395984+00:00
-- url     : https://prove2.me/theorems/00d5aaad-4fe3-44e3-bb7f-ba18f80d5d0d
-- title:
--   Theorem 1: twisting invariance
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $|\psi\rangle_{ABA'B'E}$ be a unit purification and let $U=\sum_{ij}|ij\rangle\langle ij|\otimes U_{ij}$, where every $U_{ij}$ is unitary on the shield $A'B'$. Measure $AB$ in $B$ and trace out the shield; denote this operation on the pure-state density by $\mathcal M_B$. Then
--
--   $$\mathcal M_B((U\otimes I_E)|\psi\rangle\langle\psi|(U^\dagger\otimes I_E))=\mathcal M_B(|\psi\rangle\langle\psi|).$$
--
--   Thus twisting preserves the complete measured ccq operator, including its correlations with the same Eve.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 5, Theorem 1: twisting invariance

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF pp.5–6, Theorem 1: the SAME unit purification is transported by twisting. -/
theorem twisting_invariance {d : ℕ} [NeZero d] {S T E : Type*}
    [Fintype S] [Fintype T] [Fintype E] [Nonempty S] [Nonempty T] [Nonempty E]
    (psi : EuclideanSpace ℂ ((Key d × (S × T)) × E)) (hpsi : IsState psi)
    (U : Key d → Matrix.unitaryGroup (S × T) ℂ) :
    associatedCCQ (twistPurification U psi) = associatedCCQ psi := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
