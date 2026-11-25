-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Form_U_Atom_comap_lat
-- name    : PositivityTheory.RgUd.Form.U.Atom.comap_lat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:57.046203+00:00
-- url     : https://prove2.me/theorems/35c892c5-b3cb-42d4-88be-95b569b38d53
-- title:
--   Atom: comap lat
-- statement:
--   The Atom construction uses the comap lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/IsotropicAtoms/ChartRestriction.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/IsotropicAtoms/ChartRestriction.lean#L116-L120

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem PositivityTheory.RgUd.Form.U.Atom.comap_lat (n : ℕ) (g : Matrix (Fin n) (Fin n) k) (hg : IsUnit g) (A : AddSubgroup (Fin n → k))
    (hA : IsCompact (A : Set (Fin n → k))) (hA' : IsOpen (A : Set (Fin n → k))) :
    IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧
      IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by sorry
