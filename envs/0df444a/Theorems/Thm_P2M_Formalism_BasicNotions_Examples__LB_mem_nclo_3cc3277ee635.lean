-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_mem_nclo_3cc3277ee635
-- name    : P2M_Formalism_BasicNotions_Examples__LB_mem_nclo_3cc3277ee635
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:19:41.095326+00:00
-- url     : https://prove2.me/theorems/023a78f2-b3e6-49aa-8999-63a9a0d02256
-- title:
--   P2 M Formalism Basic Notions Examples  LB mem nclo 3cc3277ee635: P2 M Formalism Basic Notions Examples  LB mem nclo 3cc3277ee635
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB mem nclo 3cc3277ee635 construction uses the P2 M Formalism Basic Notions Examples  LB mem nclo 3cc3277ee635 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocD.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocD.lean#L58-L60

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CovariantDegrees
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
  {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

theorem P2M_Formalism_BasicNotions_Examples__LB_mem_nclo_3cc3277ee635 (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
    (τ : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) : τ x ∈ (nclo K).1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«mem_nclo» := P2M_Formalism_BasicNotions_Examples__LB_mem_nclo_3cc3277ee635
