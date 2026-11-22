-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd
-- name    : P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:46.066279+00:00
-- url     : https://prove2.me/theorems/4280c5ba-ba93-4b51-a5e2-8ed9a5cc86ee
-- title:
--   P2 M Reciprocity Theory Gal Cont Action comp  44f330b68efd: P2 M Reciprocity Theory Gal Cont Action comp  44f330b68efd
-- statement:
--   The P2 M Reciprocity Theory Gal Cont Action comp  44f330b68efd construction uses the P2 M Reciprocity Theory Gal Cont Action comp  44f330b68efd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCohDefs.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCohDefs.lean#L91-L95

import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd [TopologicalSpace Γ] {D : Type*} [Group D] [TopologicalSpace D]
    {rho : Representation R Γ M} (h : ContAction rho) {φ : D →* Γ} (hφ : Continuous φ) :
    ContAction (rho.comp φ) := by sorry

alias «ReciprocityTheory».«Gal».«ContAction».«comp'» := P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd
