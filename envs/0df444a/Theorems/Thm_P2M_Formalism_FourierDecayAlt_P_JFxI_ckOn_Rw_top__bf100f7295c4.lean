-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxI_ckOn_Rw_top__bf100f7295c4
-- name    : P2M_Formalism_FourierDecayAlt_P_JFxI_ckOn_Rw_top__bf100f7295c4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:26.15912+00:00
-- url     : https://prove2.me/theorems/934b8673-0bcc-421e-ac93-55e22d038003
-- title:
--   P2 M Formalism Fourier Decay Alt P JFx I ck On Rw top  bf100f7295c4: P2 M Formalism Fourier Decay Alt P JFx I ck On Rw top  bf100f7295c4
-- statement:
--   The P2 M Formalism Fourier Decay Alt P JFx I ck On Rw top  bf100f7295c4 construction uses the P2 M Formalism Fourier Decay Alt P JFx I ck On Rw top  bf100f7295c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L104-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L104-L113

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_JFxI_ckOn_Rw_top__bf100f7295c4 {UU : Set (Mat k r)} {f : Mat k r → E} (h : CkOn ⊤ UU f) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → CkOn ⊤ UU (Rw w f) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«JFxI».«ckOn_Rw_top'» := P2M_Formalism_FourierDecayAlt_P_JFxI_ckOn_Rw_top__bf100f7295c4
