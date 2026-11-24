-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreDegree_eq_7b64163691ae
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreDegree_eq_7b64163691ae
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:11.648275+00:00
-- url     : https://prove2.me/theorems/6b4e186d-6bbe-4ca3-8b62-deb8b0046c09
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top fibre Degree eq 7b64163691ae: P2 M Ground Theory Heights  Heights Rest Terms Top fibre Degree eq 7b64163691ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top fibre Degree eq 7b64163691ae construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top fibre Degree eq 7b64163691ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L100-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L100-L126

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreDegree_eq_7b64163691ae (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ) (c : SmallBlock) (hr : 1 ≤ r)
    (ha : 1 ≤ a) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (c0 : ℚ)
    (hInt : ∀ H : RootRing f (r + a), H.IsHomogeneous (topDegree f (r + a)) →
      algebraMap ℚ (FractionRing (RootRing f (r + a))) (flagIntegral f (r + a) H) =
        algebraMap ℚ (FractionRing (RootRing f (r + a))) c0 * dividedDifference f (r + a) H) :
    fibreDegree f r a c =
      c0 * κ ^ f * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
        (numStandardTable (rectangle r a) : ℚ) ^ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«fibreDegree_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreDegree_eq_7b64163691ae
