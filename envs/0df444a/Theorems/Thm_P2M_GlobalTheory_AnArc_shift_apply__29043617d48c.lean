-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AnArc_shift_apply__29043617d48c
-- name    : P2M_GlobalTheory_AnArc_shift_apply__29043617d48c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:22.373175+00:00
-- url     : https://prove2.me/theorems/75c85924-859a-4866-b480-304771e8d560
-- title:
--   P2 M Global Theory An Arc shift apply  29043617d48c: P2 M Global Theory An Arc shift apply  29043617d48c
-- statement:
--   The P2 M Global Theory An Arc shift apply  29043617d48c construction uses the P2 M Global Theory An Arc shift apply  29043617d48c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L291-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L291-L293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable (k : ℕ) [NeZero k]

theorem P2M_GlobalTheory_AnArc_shift_apply__29043617d48c (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (z : Fin A.gB → ℂ) :
    A.shift k la α th z = eTwoPi ((A.P0 la).1 α / k) * Complex.exp (-(Real.pi * A.H z la.l)) *
      th (z + (k : ℂ)⁻¹ • (A.P0 la).2) := by sorry

alias «GlobalTheory».«AnArc».«shift_apply'» := P2M_GlobalTheory_AnArc_shift_apply__29043617d48c
