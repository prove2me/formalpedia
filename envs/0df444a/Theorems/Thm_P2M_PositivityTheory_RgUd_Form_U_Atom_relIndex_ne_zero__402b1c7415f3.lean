-- Prove2me | Theorems.Thm_P2M_PositivityTheory_RgUd_Form_U_Atom_relIndex_ne_zero__402b1c7415f3
-- name    : P2M_PositivityTheory_RgUd_Form_U_Atom_relIndex_ne_zero__402b1c7415f3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:50.601803+00:00
-- url     : https://prove2.me/theorems/c5bbf885-c07e-4767-b81d-79718299406b
-- title:
--   P2 M Positivity Theory Rg Ud Form U Atom rel Index ne zero  402b1c7415f3: P2 M Positivity Theory Rg Ud Form U Atom rel Index ne zero  402b1c7415f3
-- statement:
--   The P2 M Positivity Theory Rg Ud Form U Atom rel Index ne zero  402b1c7415f3 construction uses the P2 M Positivity Theory Rg Ud Form U Atom rel Index ne zero  402b1c7415f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/IsotropicAtoms/ChartRestriction.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/IsotropicAtoms/ChartRestriction.lean#L77-L79

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
variable [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem P2M_PositivityTheory_RgUd_Form_U_Atom_relIndex_ne_zero__402b1c7415f3 (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X)) (hHA : H ≤ A) :
    H.relIndex A ≠ 0 := by sorry

alias «PositivityTheory».«RgUd».«Form».«U».«Atom».«relIndex_ne_zero'» := P2M_PositivityTheory_RgUd_Form_U_Atom_relIndex_ne_zero__402b1c7415f3
