-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_Pe_sym__647cdd861ec3
-- name    : P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_Pe_sym__647cdd861ec3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:46.866266+00:00
-- url     : https://prove2.me/theorems/10e66c69-78c5-4ad3-8918-a2a6369e9ec1
-- title:
--   P2 M Formalism Fourier Decay Alt P Stationary Phase Model E Pe sym  647cdd861ec3: P2 M Formalism Fourier Decay Alt P Stationary Phase Model E Pe sym  647cdd861ec3
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Stationary Phase Model E Pe sym  647cdd861ec3 construction uses the P2 M Formalism Fourier Decay Alt P Stationary Phase Model E Pe sym  647cdd861ec3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2266-L2271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2266-L2271

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {a₀ : V} {ℓ : (Fin d → ℂ) →L[ℝ] V}

theorem P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_Pe_sym__647cdd861ec3 (hr : 0 < r) (hph : E_Phase d r Γ c₁ φ) (hρr : ρ ≤ r) (hτ : 0 < τ) (hτ1 : τ ≤ 1) {N : ℕ}
    (hN : N ≤ d + 6) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) ρ) (wt (Real.sqrt τ)) 4 N
      ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) (E_Pe φ) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«StationaryPhaseModel».«E_Pe_sym'» := P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_Pe_sym__647cdd861ec3
