-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_mkF_chartMonomial_ne_zero_b5c3c1e12aff
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_mkF_chartMonomial_ne_zero_b5c3c1e12aff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:35.099193+00:00
-- url     : https://prove2.me/theorems/9c2bdddd-32a3-5c29-81fc-0b2fb2c385fa
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections mk F chart Monomial ne zero b5c3c1e12aff: P2 M Ground Theory Heights  Heights Small Sections mk F chart Monomial ne zero b5c3c1e12aff
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections mk F chart Monomial ne zero b5c3c1e12aff construction uses the P2 M Ground Theory Heights  Heights Small Sections mk F chart Monomial ne zero b5c3c1e12aff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L69-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SmallSections_mkF_chartMonomial_ne_zero_b5c3c1e12aff {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    (d : ι → ℕ) : P.mkF (chartMonomial c d) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«mkF_chartMonomial_ne_zero» := P2M_GroundTheory_Heights__Heights_SmallSections_mkF_chartMonomial_ne_zero_b5c3c1e12aff
