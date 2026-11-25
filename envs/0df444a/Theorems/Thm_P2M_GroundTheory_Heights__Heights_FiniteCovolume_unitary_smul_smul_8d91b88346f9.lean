-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_smul_8d91b88346f9
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_smul_8d91b88346f9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:55.638631+00:00
-- url     : https://prove2.me/theorems/90d521b2-bce4-4407-8373-1f015c240dc0
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume unitary smul smul 8d91b88346f9: P2 M Ground Theory Heights  Heights Finite Covolume unitary smul smul 8d91b88346f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume unitary smul smul 8d91b88346f9 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume unitary smul smul 8d91b88346f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean#L54-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceUnitsFiniteIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVectorOrbitsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_smul_8d91b88346f9 {h : HermitianForm F E W} (γ : h.unitaryGroup) (c : E) (w : W) :
    γ • (c • w) = c • (γ • w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«unitary_smul_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_smul_8d91b88346f9
