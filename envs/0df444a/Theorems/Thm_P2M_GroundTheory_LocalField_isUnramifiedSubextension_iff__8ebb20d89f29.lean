-- Prove2me | Theorems.Thm_P2M_GroundTheory_LocalField_isUnramifiedSubextension_iff__8ebb20d89f29
-- name    : P2M_GroundTheory_LocalField_isUnramifiedSubextension_iff__8ebb20d89f29
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:15.768463+00:00
-- url     : https://prove2.me/theorems/744d6810-bf8e-514f-84f9-9eae8f19e9b4
-- title:
--   P2 M Ground Theory Local Field is Unramified Subextension iff  8ebb20d89f29: P2 M Ground Theory Local Field is Unramified Subextension iff  8ebb20d89f29
-- statement:
--   The P2 M Ground Theory Local Field is Unramified Subextension iff  8ebb20d89f29 construction uses the P2 M Ground Theory Local Field is Unramified Subextension iff  8ebb20d89f29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/TameExtension.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/TameExtension.lean#L84-L87

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
import Definitions.Def_GroundTheory_LocalFields_RamificationTameStructure
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_TameExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IntermediateField ValuativeRel
open GroundTheory GroundTheory.LocalField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem P2M_GroundTheory_LocalField_isUnramifiedSubextension_iff__8ebb20d89f29 (E : IntermediateField K Ω) [FiniteDimensional K E] :
    IsUnramifiedSubextension E ↔ ramificationIndex K E = 1 := by sorry

alias «GroundTheory».«LocalField».«isUnramifiedSubextension_iff'» := P2M_GroundTheory_LocalField_isUnramifiedSubextension_iff__8ebb20d89f29
