-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_exists_ext_b6f487c55f36
-- name    : P2M_Formalism_BasicNotions_Examples__LB_exists_ext_b6f487c55f36
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:19.298055+00:00
-- url     : https://prove2.me/theorems/89a7bddd-941d-44a6-8b7f-8858528d825d
-- title:
--   P2 M Formalism Basic Notions Examples  LB exists ext b6f487c55f36: P2 M Formalism Basic Notions Examples  LB exists ext b6f487c55f36
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB exists ext b6f487c55f36 construction uses the P2 M Formalism Basic Notions Examples  LB exists ext b6f487c55f36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean#L116-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean#L116-L159

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
include hj

theorem P2M_Formalism_BasicNotions_Examples__LB_exists_ext_b6f487c55f36 (g : G E Ω) (hg : g ∈ Dec (F := E) A) :
    ∃ σ : GQ l, ∀ x, σ (j x) = j (g x) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«exists_ext» := P2M_Formalism_BasicNotions_Examples__LB_exists_ext_b6f487c55f36
