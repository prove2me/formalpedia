-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxDs3_unit_lr__0fb147390fef
-- name    : P2M_Formalism_FourierDecayAlt_P_JFxDs3_unit_lr__0fb147390fef
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:37:51.379576+00:00
-- url     : https://prove2.me/theorems/06bb3931-867f-4c0b-90e3-9bce39822316
-- title:
--   P2 M Formalism Fourier Decay Alt P JFx Ds3 unit lr  0fb147390fef: P2 M Formalism Fourier Decay Alt P JFx Ds3 unit lr  0fb147390fef
-- statement:
--   The P2 M Formalism Fourier Decay Alt P JFx Ds3 unit lr  0fb147390fef construction uses the P2 M Formalism Fourier Decay Alt P JFx Ds3 unit lr  0fb147390fef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselDomainMeasurable.lean#L157-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselDomainMeasurable.lean#L157-L164

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem P2M_Formalism_FourierDecayAlt_P_JFxDs3_unit_lr__0fb147390fef {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X) :
    ∀ x ∈ lr u v, unitLie k r x.2 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«JFxDs3».«unit_lr'» := P2M_Formalism_FourierDecayAlt_P_JFxDs3_unit_lr__0fb147390fef
