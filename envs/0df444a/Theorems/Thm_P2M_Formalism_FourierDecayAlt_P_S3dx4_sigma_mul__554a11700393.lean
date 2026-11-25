-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_S3dx4_sigma_mul__554a11700393
-- name    : P2M_Formalism_FourierDecayAlt_P_S3dx4_sigma_mul__554a11700393
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:30.899057+00:00
-- url     : https://prove2.me/theorems/ee134d47-ac77-4b04-ac2d-659616908cb1
-- title:
--   P2 M Formalism Fourier Decay Alt P S3dx4 sigma mul  554a11700393: P2 M Formalism Fourier Decay Alt P S3dx4 sigma mul  554a11700393
-- statement:
--   The P2 M Formalism Fourier Decay Alt P S3dx4 sigma mul  554a11700393 construction uses the P2 M Formalism Fourier Decay Alt P S3dx4 sigma mul  554a11700393 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMemMeasurableSet.lean#L33-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UhMemMeasurableSet.lean#L33-L51

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbConvDDOfDecDD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMemMeasurableSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_S3dx4_sigma_mul__554a11700393 {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) {a b : Mx k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ (a * b) = (σ a).comp (σ b) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«S3dx4».«sigma_mul'» := P2M_Formalism_FourierDecayAlt_P_S3dx4_sigma_mul__554a11700393
