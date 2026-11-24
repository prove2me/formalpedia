-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isRegularSection_form_6765ee38e78f
-- name    : P2M_GroundTheory_Heights__Heights_Model_isRegularSection_form_6765ee38e78f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:31.501959+00:00
-- url     : https://prove2.me/theorems/bb2cdc3d-ac76-404c-8442-505166d26524
-- title:
--   P2 M Ground Theory Heights  Heights Model is Regular Section form 6765ee38e78f: P2 M Ground Theory Heights  Heights Model is Regular Section form 6765ee38e78f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model is Regular Section form 6765ee38e78f construction uses the P2 M Ground Theory Heights  Heights Model is Regular Section form 6765ee38e78f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L232-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L232-L238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_isRegularSection_form_6765ee38e78f {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    {P : Ideal (MRing ι F)} (hP : P.IsPrime) {a : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s a)
    (hsP : s ∉ P) : IsRegularSection P (fun k => (a k : ℤ)) s 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«isRegularSection_form» := P2M_GroundTheory_Heights__Heights_Model_isRegularSection_form_6765ee38e78f
