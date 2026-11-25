-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAtHom_apply_5d779c7499d4
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAtHom_apply_5d779c7499d4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:49:41.776334+00:00
-- url     : https://prove2.me/theorems/ba994a85-4b3e-44f4-ac3e-77db84b82f49
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume vec At Hom apply 5d779c7499d4: P2 M Ground Theory Heights  Heights Finite Covolume vec At Hom apply 5d779c7499d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume vec At Hom apply 5d779c7499d4 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume vec At Hom apply 5d779c7499d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StArchCovolumeBound.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StArchCovolumeBound.lean#L20-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StArchCovolumeBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [IsTotallyComplex E] [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAtHom_apply_5d779c7499d4 (v : Basis ι E W) (x : W) : vecAtHom v x = vecAt v x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«vecAtHom_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAtHom_apply_5d779c7499d4
