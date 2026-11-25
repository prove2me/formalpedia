-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxI_ckOn_RdV__1ba0d0d897b8
-- name    : P2M_Formalism_FourierDecayAlt_P_JFxI_ckOn_RdV__1ba0d0d897b8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:09:32.230957+00:00
-- url     : https://prove2.me/theorems/543b05aa-a5d2-59de-9327-ee21f48d2753
-- title:
--   P2 M Formalism Fourier Decay Alt P JFx I ck On Rd V  1ba0d0d897b8: P2 M Formalism Fourier Decay Alt P JFx I ck On Rd V  1ba0d0d897b8
-- statement:
--   The P2 M Formalism Fourier Decay Alt P JFx I ck On Rd V  1ba0d0d897b8 construction uses the P2 M Formalism Fourier Decay Alt P JFx I ck On Rd V  1ba0d0d897b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L73-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L73-L83

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

theorem P2M_Formalism_FourierDecayAlt_P_JFxI_ckOn_RdV__1ba0d0d897b8 {m : ℕ∞} {UU : Set (Mat k r)} {f : Mat k r → E} {X : Mat k r} (hX : inLie k r X)
    (h : CkOn (m + 1) UU f) : CkOn m UU (RdV X f) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«JFxI».«ckOn_RdV'» := P2M_Formalism_FourierDecayAlt_P_JFxI_ckOn_RdV__1ba0d0d897b8
