-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_not_dvd_prod_erase_35fbca75cdeb
-- name    : P2M_GroundTheory_Heights__Heights_Model_not_dvd_prod_erase_35fbca75cdeb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:19.83128+00:00
-- url     : https://prove2.me/theorems/e14d8e1b-3ffa-4a35-937f-707a68a307d8
-- title:
--   P2 M Ground Theory Heights  Heights Model not dvd prod erase 35fbca75cdeb: P2 M Ground Theory Heights  Heights Model not dvd prod erase 35fbca75cdeb
-- statement:
--   The P2 M Ground Theory Heights  Heights Model not dvd prod erase 35fbca75cdeb construction uses the P2 M Ground Theory Heights  Heights Model not dvd prod erase 35fbca75cdeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L29-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_not_dvd_prod_erase_35fbca75cdeb (S : Finset Nat.Primes) (p : Nat.Primes) :
    ¬ (p : ℕ) ∣ ∏ q ∈ S.erase p, (q : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«not_dvd_prod_erase» := P2M_GroundTheory_Heights__Heights_Model_not_dvd_prod_erase_35fbca75cdeb
