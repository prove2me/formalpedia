-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Tree_premises_satisfiable__242a85f84517
-- name    : P2M_Formalism_L2_Indef_Tree_premises_satisfiable__242a85f84517
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:47.475294+00:00
-- url     : https://prove2.me/theorems/b2dd97b1-298e-4319-b22c-2e47c5844ee7
-- title:
--   P2 M Formalism L2 Indef Tree premises satisfiable  242a85f84517: P2 M Formalism L2 Indef Tree premises satisfiable  242a85f84517
-- statement:
--   The P2 M Formalism L2 Indef Tree premises satisfiable  242a85f84517 construction uses the P2 M Formalism L2 Indef Tree premises satisfiable  242a85f84517 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/IndefiniteTreeX.lean#L273-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/IndefiniteTreeX.lean#L273-L290

import Mathlib
import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_HarderNarasimhan_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_ExistsCoordBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_KernelExtensionOfKoszulLoweringImageLeviWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Decomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ProjKillsLiPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_OfListTakeOfFn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuasiRegularSequence_RegularSequencePowerExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MiracleFlatness_MiracleFlatOfRegSeqDepth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_ExistsIsRegularOfListEqMaximalIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MiracleFlatness_MulXProjQExact
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_EagonNorthcottExactOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_AugmentationDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionLowersSecondDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZeroOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_BasisZeroEqSingle
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_CardFilterLtInsert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_LatticeInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StBaseOf
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
universe u
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open scoped InnerProductSpace

theorem P2M_Formalism_L2_Indef_Tree_premises_satisfiable__242a85f84517 :
    (7 % 16 = 7 ∧ Squarefree 7) ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, |(Polynomial.X : Polynomial ℝ).eval x| ≤ 1) ∧
    0 < Complex.I.im ∧ 0 < (Complex.I / 1).im ∧ (reducedForms (-4)).Nonempty ∧
    RingTheory.Sequence.IsWeaklyRegular ℤ (List.ofFn (fun _ : Fin 1 => (2 : ℤ))) ∧
    RingTheory.Sequence.IsRegular ℤ ([] : List ℤ) ∧
    (∀ z : Fin 1 → ℂ_[2], (∀ i, ‖z i‖ < 1) →
      Summable (fun α : Fin 1 →₀ ℕ => (0 : ℂ_[2]) * ∏ i, z i ^ α i) ∧
      ‖∑' α : Fin 1 →₀ ℕ, (0 : ℂ_[2]) * ∏ i, z i ^ α i‖ ≤ 1) := by sorry

alias «Formalism».«L2».«Indef».«Tree».«premises_satisfiable₂» := P2M_Formalism_L2_Indef_Tree_premises_satisfiable__242a85f84517
