-- Prove2me | Theorems.Thm_UpperTheory_V_conjGal_apply
-- name    : UpperTheory.V.conjGal_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:10.03701+00:00
-- url     : https://prove2.me/theorems/6492c0d2-ecd1-4084-b893-a5e3b34fe9a0
-- title:
--   V: conj Gal apply
-- statement:
--   The V construction uses the conj Gal apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PartsConj.lean#L40-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PartsConj.lean#L40-L40

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
open UpperTheory UpperTheory.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable {τ : F ≃+* F} {σ : Ω ≃+* Ω}
omit [NumberField F]

theorem UpperTheory.V.conjGal_apply (h : IsLift τ σ) (g : G F Ω) (x : Ω) : conjGal h g x = σ.symm (g (σ x)) := by sorry
