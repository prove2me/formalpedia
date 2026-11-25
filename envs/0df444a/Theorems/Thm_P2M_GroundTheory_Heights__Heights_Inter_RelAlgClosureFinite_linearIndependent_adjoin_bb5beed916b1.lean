-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RelAlgClosureFinite_linearIndependent_adjoin_bb5beed916b1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RelAlgClosureFinite_linearIndependent_adjoin_bb5beed916b1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:34.095704+00:00
-- url     : https://prove2.me/theorems/52aca611-bb9b-4345-8368-332ea15febcc
-- title:
--   P2 M Ground Theory Heights  Heights Inter Rel Alg Closure Finite linear Independent adjoin bb5beed916b1: P2 M Ground Theory Heights  Heights Inter Rel Alg Closure Finite linear Independent adjoin bb5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Rel Alg Closure Finite linear Independent adjoin bb5beed916b1 construction uses the P2 M Ground Theory Heights  Heights Inter Rel Alg Closure Finite linear Independent adjoin bb5beed916b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRelAlgClosureFinite.lean#L11-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRelAlgClosureFinite.lean#L11-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRelAlgClosureFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRelAlgClosureFinite
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial IntermediateField.algebraAdjoinAdjoin

theorem P2M_GroundTheory_Heights__Heights_Inter_RelAlgClosureFinite_linearIndependent_adjoin_bb5beed916b1 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) {σ : Type*} {x : σ → L} (hx : AlgebraicIndependent M x)
    {ι : Type*} {m : ι → M} (hm : LinearIndependent K m) :
    LinearIndependent (Algebra.adjoin K (Set.range x)) (fun i => (m i : L)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RelAlgClosureFinite».«linearIndependent_adjoin» := P2M_GroundTheory_Heights__Heights_Inter_RelAlgClosureFinite_linearIndependent_adjoin_bb5beed916b1
