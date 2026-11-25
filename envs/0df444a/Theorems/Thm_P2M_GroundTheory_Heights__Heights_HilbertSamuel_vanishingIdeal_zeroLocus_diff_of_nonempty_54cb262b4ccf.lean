-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_vanishingIdeal_zeroLocus_diff_of_nonempty_54cb262b4ccf
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_vanishingIdeal_zeroLocus_diff_of_nonempty_54cb262b4ccf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:25.390078+00:00
-- url     : https://prove2.me/theorems/5493c1f4-7801-42b5-835c-ff4d833d24c3
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel vanishing Ideal zero Locus diff of nonempty 54cb262b4ccf: P2 M Ground Theory Heights  Heights Hilbert Samuel vanishing Ideal zero Locus diff of nonem
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel vanishing Ideal zero Locus diff of nonempty 54cb262b4ccf construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel vanishing Ideal zero Locus diff of nonempty 54cb262b4ccf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PClopenComponents.lean#L14-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PClopenComponents.lean#L14-L32

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_vanishingIdeal_zeroLocus_diff_of_nonempty_54cb262b4ccf {σ : Type} [Fintype σ]
    (W J : Ideal (MvPolynomial σ ℂ)) [hW : W.IsPrime]
    (hne : (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty) :
    vanishingIdeal ℂ (zeroLocus ℂ W \ zeroLocus ℂ J) = W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«vanishingIdeal_zeroLocus_diff_of_nonempty» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_vanishingIdeal_zeroLocus_diff_of_nonempty_54cb262b4ccf
