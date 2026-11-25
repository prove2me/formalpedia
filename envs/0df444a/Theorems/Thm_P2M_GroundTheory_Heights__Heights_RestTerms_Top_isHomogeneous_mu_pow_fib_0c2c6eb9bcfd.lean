-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_mu_pow_fib_0c2c6eb9bcfd
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_mu_pow_fib_0c2c6eb9bcfd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:40.176715+00:00
-- url     : https://prove2.me/theorems/f128d84d-fe3f-4fb7-bf5c-563a425bc2fe
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous mu pow fib 0c2c6eb9bcfd: P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous mu pow fib 0c2c6eb9bcfd
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous mu pow fib 0c2c6eb9bcfd construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous mu pow fib 0c2c6eb9bcfd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L64-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_mu_pow_fib_0c2c6eb9bcfd (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ)
    (c : SmallBlock) :
    (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c).IsHomogeneous
      (topDegree f (r + a)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«isHomogeneous_mu_pow_fib» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_mu_pow_fib_0c2c6eb9bcfd
