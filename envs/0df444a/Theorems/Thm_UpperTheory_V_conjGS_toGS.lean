-- Prove2me | Theorems.Thm_UpperTheory_V_conjGS_toGS
-- name    : UpperTheory.V.conjGS_toGS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:35.606804+00:00
-- url     : https://prove2.me/theorems/a2e984cf-e95a-4ef4-be76-fc43af9752bf
-- title:
--   V: conj GS to GS
-- statement:
--   The V construction uses the conj GS to GS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PartsConj.lean#L125-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PartsConj.lean#L125-L126

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
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem UpperTheory.V.conjGS_toGS (D : LData F Ω l) (h : IsLift τ σ) (g : G F Ω) :
    conjGS D h (toGS Ω _ g) = toGS Ω _ (conjGal h g) := by sorry
