-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_fracEval_algebraMap_cf6041a4f59e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_fracEval_algebraMap_cf6041a4f59e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:45:01.785683+00:00
-- url     : https://prove2.me/theorems/781c18b4-1782-4d5a-8d6b-846980fd70eb
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac frac Eval algebra Map cf6041a4f59e: P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac frac Eval algebra Map cf6041a4f59e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac frac Eval algebra Map cf6041a4f59e construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Rank Frac frac Eval algebra Map cf6041a4f59e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankFrac.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocRankFrac.lean#L77-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
  (x' : (Σ k, ι' k) → Ω) (P' : Ideal (MRing ι')) [P'.IsPrime]
  (h : RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω) = P')

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_fracEval_algebraMap_cf6041a4f59e (f : MRing ι') :
    fracEval x' P' h (algebraMap _ _ (Ideal.Quotient.mk P' f)) = aeval x' f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocRankFrac».«fracEval_algebraMap» := P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_fracEval_algebraMap_cf6041a4f59e
