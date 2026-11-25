-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeZariskiDense_eval_eq_zero_of_mem_map_c9c7b8d71cbd
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeZariskiDense_eval_eq_zero_of_mem_map_c9c7b8d71cbd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:33.096268+00:00
-- url     : https://prove2.me/theorems/e292c378-471c-4926-8d5d-35d4af56f82f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Zariski Dense eval eq zero of mem map c9c7b8d71cbd: P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Zariski Dense eval eq zero of mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Zariski Dense eval eq zero of mem map c9c7b8d71cbd construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Prime Zariski Dense eval eq zero of mem map c9c7b8d71cbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPrimeZariskiDense.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPrimeZariskiDense.lean#L14-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexFormsOnPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexMinimalPrimesContract
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPrimeZariskiDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeZariskiDense_eval_eq_zero_of_mem_map_c9c7b8d71cbd {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {F : MvPolynomial (Σ k, ι k) ℂ}
    (hF : F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))) : eval z F = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«PrimeZariskiDense».«eval_eq_zero_of_mem_map» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeZariskiDense_eval_eq_zero_of_mem_map_c9c7b8d71cbd
