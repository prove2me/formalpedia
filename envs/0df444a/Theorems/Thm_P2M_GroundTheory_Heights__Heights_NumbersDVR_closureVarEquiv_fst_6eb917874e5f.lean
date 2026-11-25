-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_closureVarEquiv_fst_6eb917874e5f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_closureVarEquiv_fst_6eb917874e5f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:27.423366+00:00
-- url     : https://prove2.me/theorems/6afea8aa-59b4-4037-97de-7ed7230a05bc
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR closure Var Equiv fst 6eb917874e5f: P2 M Ground Theory Heights  Heights Numbers DVR closure Var Equiv fst 6eb917874e5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR closure Var Equiv fst 6eb917874e5f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR closure Var Equiv fst 6eb917874e5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L47-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable (K : Type*)
variable {K} (ι : K → Type) (M M' : ℕ)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_closureVarEquiv_fst_6eb917874e5f (v : Σ o, bundleIdx (bundleIdx ι M) M' o) :
    (closureVarEquiv ι M M' v).1 = closureBlockEquiv K v.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«closureVarEquiv_fst» := P2M_GroundTheory_Heights__Heights_NumbersDVR_closureVarEquiv_fst_6eb917874e5f
