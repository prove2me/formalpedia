-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_maDens_log_dualNorm_sheet_6715060231bc
-- name    : P2M_GroundTheory_Heights__Heights_maDens_log_dualNorm_sheet_6715060231bc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:54:53.071796+00:00
-- url     : https://prove2.me/theorems/c897bb9a-4710-5e6a-92cc-925d34543c4a
-- title:
--   P2 M Ground Theory Heights  Heights ma Dens log dual Norm sheet 6715060231bc: P2 M Ground Theory Heights  Heights ma Dens log dual Norm sheet 6715060231bc
-- statement:
--   The P2 M Ground Theory Heights  Heights ma Dens log dual Norm sheet 6715060231bc construction uses the P2 M Ground Theory Heights  Heights ma Dens log dual Norm sheet 6715060231bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConePolar.lean#L20-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConePolar.lean#L20-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeChartGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartGramMA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConePolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_maDens_log_dualNorm_sheet_6715060231bc {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (A : Matrix (Fin e) (Fin n) ℂ) (y : Fin e → ℂ) (x : Fin n → ℂ)
    (s : (Fin e → ℂ) → Fin n → ℂ) (hx : x ∈ fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y)
    (hs : IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s) :
    ReciprocityTheory.AnForm.maDens (fun k => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) y =
      (e.factorial : ℝ) / Real.pi ^ e * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y /
        h.dualNorm x ^ (2 * (e + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«maDens_log_dualNorm_sheet» := P2M_GroundTheory_Heights__Heights_maDens_log_dualNorm_sheet_6715060231bc
