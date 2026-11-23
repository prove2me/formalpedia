-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HeckeGal_continuous_of_isOpen_ker__a1c5cff15c2b
-- name    : P2M_GlobalTheory_HeckeGal_continuous_of_isOpen_ker__a1c5cff15c2b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:47.43372+00:00
-- url     : https://prove2.me/theorems/c6acef41-393c-42ac-a624-2ff4469e86cc
-- title:
--   P2 M Global Theory Hecke Gal continuous of is Open ker  a1c5cff15c2b: P2 M Global Theory Hecke Gal continuous of is Open ker  a1c5cff15c2b
-- statement:
--   The P2 M Global Theory Hecke Gal continuous of is Open ker  a1c5cff15c2b construction uses the P2 M Global Theory Hecke Gal continuous of is Open ker  a1c5cff15c2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L374-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L374-L379

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

theorem P2M_GlobalTheory_HeckeGal_continuous_of_isOpen_ker__a1c5cff15c2b {Γ B : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (φ : Γ →* B) (h : IsOpen (φ.ker : Set Γ)) : Continuous φ := by sorry

alias «GlobalTheory».«HeckeGal».«continuous_of_isOpen_ker'» := P2M_GlobalTheory_HeckeGal_continuous_of_isOpen_ker__a1c5cff15c2b
