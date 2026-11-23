-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RealWeil_UnitaryOsc_detPlus_conj__6463fe3cfaa2
-- name    : P2M_GlobalTheory_RealWeil_UnitaryOsc_detPlus_conj__6463fe3cfaa2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:28.192416+00:00
-- url     : https://prove2.me/theorems/98da5062-ced9-4f0a-8a8b-ce8dfd8e0182
-- title:
--   P2 M Global Theory Real Weil Unitary Osc det Plus conj  6463fe3cfaa2: P2 M Global Theory Real Weil Unitary Osc det Plus conj  6463fe3cfaa2
-- statement:
--   The P2 M Global Theory Real Weil Unitary Osc det Plus conj  6463fe3cfaa2 construction uses the P2 M Global Theory Real Weil Unitary Osc det Plus conj  6463fe3cfaa2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionUnitaryGroupHermitian.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionUnitaryGroupHermitian.lean#L52-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.UnitaryOsc
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem P2M_GlobalTheory_RealWeil_UnitaryOsc_detPlus_conj__6463fe3cfaa2 {a s s' g g' : Matrix ι ι ℂ} (ha : a.det ≠ 0) (hs : a * s = s' * a) (hg : a * g = g' * a) :
    dP s g = dP s' g' := by sorry

alias «GlobalTheory».«RealWeil».«UnitaryOsc».«detPlus_conj₂» := P2M_GlobalTheory_RealWeil_UnitaryOsc_detPlus_conj__6463fe3cfaa2
