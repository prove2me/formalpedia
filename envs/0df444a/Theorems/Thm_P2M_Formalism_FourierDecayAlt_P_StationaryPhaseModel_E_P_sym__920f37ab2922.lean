-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_sym__920f37ab2922
-- name    : P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_sym__920f37ab2922
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:12.965697+00:00
-- url     : https://prove2.me/theorems/e05fc93b-768b-457f-b892-974291fc9062
-- title:
--   P2 M Formalism Fourier Decay Alt P Stationary Phase Model E P sym  920f37ab2922: P2 M Formalism Fourier Decay Alt P Stationary Phase Model E P sym  920f37ab2922
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Stationary Phase Model E P sym  920f37ab2922 construction uses the P2 M Formalism Fourier Decay Alt P Stationary Phase Model E P sym  920f37ab2922 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2259-L2264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2259-L2264

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

theorem P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_sym__920f37ab2922 (hr : 0 < r) (hph : E_Phase d r Γ c₁ φ) (hρr : ρ ≤ r) (hτ : 0 < τ) (hτ1 : τ ≤ 1) {N : ℕ}
    (hN : N ≤ d + 6) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) ρ) (wt (Real.sqrt τ)) 3 N
      ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) (E_P φ) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«StationaryPhaseModel».«E_P_sym'» := P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_sym__920f37ab2922
