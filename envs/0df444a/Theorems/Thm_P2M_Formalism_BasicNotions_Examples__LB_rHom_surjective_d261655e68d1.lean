-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_rHom_surjective_d261655e68d1
-- name    : P2M_Formalism_BasicNotions_Examples__LB_rHom_surjective_d261655e68d1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:35:17.391615+00:00
-- url     : https://prove2.me/theorems/5af13e79-fa4e-51c6-815f-1468f5f20ceb
-- title:
--   P2 M Formalism Basic Notions Examples  LB r Hom surjective d261655e68d1: P2 M Formalism Basic Notions Examples  LB r Hom surjective d261655e68d1
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB r Hom surjective d261655e68d1 construction uses the P2 M Formalism Basic Notions Examples  LB r Hom surjective d261655e68d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean#L161-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean#L161-L184

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
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
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω]
variable [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)
variable {j} {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

theorem P2M_Formalism_BasicNotions_Examples__LB_rHom_surjective_d261655e68d1 : Function.Surjective (rHom (E := E) hj) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«rHom_surjective» := P2M_Formalism_BasicNotions_Examples__LB_rHom_surjective_d261655e68d1
