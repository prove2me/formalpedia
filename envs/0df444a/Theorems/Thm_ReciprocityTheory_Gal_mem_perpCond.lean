-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_mem_perpCond
-- name    : ReciprocityTheory.Gal.mem_perpCond
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:46.063653+00:00
-- url     : https://prove2.me/theorems/b5be6ce6-3610-425b-8c63-0cc07eb91115
-- title:
--   Gal: mem perp Cond
-- statement:
--   The Gal construction uses the mem perp Cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCohDefs.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCohDefs.lean#L119-L124

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
variable {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ)

theorem ReciprocityTheory.Gal.mem_perpCond {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (phi : ∀ i, D i →* Γ) (hrho : ∀ i, ContAction (rho.comp (phi i)))
    (L : ∀ i, Submodule R (H1 (rho.comp (phi i)))) (i : I) (y : H1 ((twDual χ rho).comp (phi i))) :
    y ∈ perpCond χ rho phi hrho L i ↔ ∀ x ∈ L i, cupH1H1TwistedDual χ rho (phi i) (hrho i) y x = 0 := by sorry
