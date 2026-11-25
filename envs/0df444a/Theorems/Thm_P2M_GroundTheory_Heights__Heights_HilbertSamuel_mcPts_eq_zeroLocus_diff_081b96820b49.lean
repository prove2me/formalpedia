-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_mcPts_eq_zeroLocus_diff_081b96820b49
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_mcPts_eq_zeroLocus_diff_081b96820b49
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:20:05.170173+00:00
-- url     : https://prove2.me/theorems/f9a5ff08-90d4-44d8-bd8e-c6fae9c37160
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel mc Pts eq zero Locus diff 081b96820b49: P2 M Ground Theory Heights  Heights Hilbert Samuel mc Pts eq zero Locus diff 081b96820b49
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel mc Pts eq zero Locus diff 081b96820b49 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel mc Pts eq zero Locus diff 081b96820b49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PClopenComponents.lean#L54-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PClopenComponents.lean#L54-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PClopenComponents
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_mcPts_eq_zeroLocus_diff_081b96820b49 (P : Ideal (MRing ι)) :
    mcPts P = zeroLocus ℂ (P.map (MvPolynomial.map (Int.castRingHom ℂ))) \
      zeroLocus ℂ (multiIrrelevantIdeal ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«mcPts_eq_zeroLocus_diff» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_mcPts_eq_zeroLocus_diff_081b96820b49
