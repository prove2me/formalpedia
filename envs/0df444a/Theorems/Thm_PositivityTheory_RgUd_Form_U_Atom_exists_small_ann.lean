-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Form_U_Atom_exists_small_ann
-- name    : PositivityTheory.RgUd.Form.U.Atom.exists_small_ann
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:18.185788+00:00
-- url     : https://prove2.me/theorems/048be628-54ec-46fd-937d-cd7f8ad56811
-- title:
--   Atom: exists small ann
-- statement:
--   The Atom construction uses the exists small ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/IsotropicAtoms/ChartRestriction.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/IsotropicAtoms/ChartRestriction.lean#L111-L114

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

theorem PositivityTheory.RgUd.Form.U.Atom.exists_small_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (n : ℕ) (S : Set (Fin n → k))
    (hS : S ∈ nhds (0 : Fin n → k)) : ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧
      ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S := by sorry
