-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial__4bb3055a91f9
-- name    : P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial__4bb3055a91f9
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:51.168451+00:00
-- url     : https://prove2.me/theorems/ebe9cd37-4766-4340-9886-107dda9565b1
-- title:
--   P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone chart Monomial  4bb3055a91f9: P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone chart Monomial  4bb3055a91f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone chart Monomial  4bb3055a91f9 construction uses the P2 M Ground Theory Heights  Heights Bounded Monomials eval Cone chart Monomial  4bb3055a91f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZero.lean#L62-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial__4bb3055a91f9 {F : Type*} [CommRing F] (z : Cone n F)
    (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BoundedMonomials».«evalCone_chartMonomial'» := P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial__4bb3055a91f9
