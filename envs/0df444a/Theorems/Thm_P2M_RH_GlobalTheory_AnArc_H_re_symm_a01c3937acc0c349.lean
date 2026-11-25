-- Prove2me | Theorems.Thm_P2M_RH_GlobalTheory_AnArc_H_re_symm_a01c3937acc0c349
-- name    : P2M_RH_GlobalTheory_AnArc_H_re_symm_a01c3937acc0c349
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:12:28.230273+00:00
-- url     : https://prove2.me/theorems/bed2b33b-800e-4b55-8ec5-c0188e88504a
-- title:
--   P2 M RH Global Theory An Arc H re symm a01c3937acc0c349: P2 M RH Global Theory An Arc H re symm a01c3937acc0c349
-- statement:
--   The P2 M RH Global Theory An Arc H re symm a01c3937acc0c349 construction uses the P2 M RH Global Theory An Arc H re symm a01c3937acc0c349 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L119-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L119-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem P2M_RH_GlobalTheory_AnArc_H_re_symm_a01c3937acc0c349 (z w : Fin A.gB → ℂ) : (A.H z w).re = (A.H w z).re := by sorry

alias «GlobalTheory».«AnArc».«H_re_symm» := P2M_RH_GlobalTheory_AnArc_H_re_symm_a01c3937acc0c349
