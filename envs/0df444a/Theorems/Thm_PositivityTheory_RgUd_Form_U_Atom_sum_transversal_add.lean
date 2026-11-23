-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Form_U_Atom_sum_transversal_add
-- name    : PositivityTheory.RgUd.Form.U.Atom.sum_transversal_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:59.10356+00:00
-- url     : https://prove2.me/theorems/4c40f50c-353a-48b2-8a44-ce456be08617
-- title:
--   Atom: sum transversal add
-- statement:
--   The Atom construction uses the sum transversal add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/IsotropicAtoms/ChartRestriction.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/IsotropicAtoms/ChartRestriction.lean#L26-L30

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenAdditiveCharacterKernelStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCompactOpenSubgroupMemStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsCompactSupAddSubgroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCosetRepresentativesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexOpenCompactNeZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenCharacterAnnihilatorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorCompactWithinNhdsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComapMulVecCompactOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLVecMulEqLastBasisStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSemidefiniteNullRadicalStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SesquilinearEqZeroOfDiagZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumTranslateInvariantStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumsProportionalCard
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_HermitianForms_UnitaryLattices_IsotropicAtoms_ChartRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd.Form.U.Atom
variable {X : Type} [AddCommGroup X]

theorem PositivityTheory.RgUd.Form.U.Atom.sum_transversal_add {M : Type} [AddCommMonoid M] {A H : AddSubgroup X} (hHA : H ≤ A) {T : Finset X}
    (hT : ∀ t ∈ T, t ∈ A) (hTr : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) (F : X → M)
    (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) {a : X} (ha : a ∈ A) :
    ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by sorry
