-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxI_rdV_hasDerivAt__ecc5ddd54a31
-- name    : P2M_Formalism_FourierDecayAlt_P_JFxI_rdV_hasDerivAt__ecc5ddd54a31
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:35.051054+00:00
-- url     : https://prove2.me/theorems/0ecf8d1b-db5e-5fac-a63c-c370e4c73866
-- title:
--   P2 M Formalism Fourier Decay Alt P JFx I rd V has Deriv At  ecc5ddd54a31: P2 M Formalism Fourier Decay Alt P JFx I rd V has Deriv At  ecc5ddd54a31
-- statement:
--   The P2 M Formalism Fourier Decay Alt P JFx I rd V has Deriv At  ecc5ddd54a31 construction uses the P2 M Formalism Fourier Decay Alt P JFx I rd V has Deriv At  ecc5ddd54a31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L115-L121

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

theorem P2M_Formalism_FourierDecayAlt_P_JFxI_rdV_hasDerivAt__ecc5ddd54a31 {UU : Set (Mat k r)} {f : Mat k r → E} (h : CkOn 1 UU f) {g X : Mat k r} (hg : g ∈ UU)
    (hgG : g ∈ GV k r) (hX : inLie k r X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (RdV X f g) 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«JFxI».«rdV_hasDerivAt'» := P2M_Formalism_FourierDecayAlt_P_JFxI_rdV_hasDerivAt__ecc5ddd54a31
