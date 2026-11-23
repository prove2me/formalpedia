-- Prove2me | Theorems.Thm_UpperTheory_V_h1TwistConjByLift_mul_apply
-- name    : UpperTheory.V.h1TwistConjByLift_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:21.132929+00:00
-- url     : https://prove2.me/theorems/1d1e76a5-c326-44c8-be23-ebd0e6d477cf
-- title:
--   V: h1 Twist Conj By Lift mul apply
-- statement:
--   The V construction uses the h1 Twist Conj By Lift mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PartsConj.lean#L181-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PartsConj.lean#L181-L200

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

theorem UpperTheory.V.h1TwistConjByLift_mul_apply (D : LData F Ω l) (e : ℤ) {τ₁ τ₂ τ₃ : F ≃+* F} {σ₁ σ₂ σ₃ : Ω ≃+* Ω} (h₁ : IsLift τ₁ σ₁)
    (h₂ : IsLift τ₂ σ₂) (h₃ : IsLift τ₃ σ₃) (hσ : σ₃ = σ₂ * σ₁) (x : H1 (qzTw D e)) :
    h1TwistConjByLift D e h₃ x = h1TwistConjByLift D e h₂ (h1TwistConjByLift D e h₁ x) := by sorry
