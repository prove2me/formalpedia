-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_norm_le_pow_1bb8f3f89542
-- name    : P2M_Formalism_BasicNotions_Examples__LB_norm_le_pow_1bb8f3f89542
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:35:58.815069+00:00
-- url     : https://prove2.me/theorems/fe105bca-6e1d-4880-b98f-952d267ad99a
-- title:
--   P2 M Formalism Basic Notions Examples  LB norm le pow 1bb8f3f89542: P2 M Formalism Basic Notions Examples  LB norm le pow 1bb8f3f89542
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB norm le pow 1bb8f3f89542 construction uses the P2 M Formalism Basic Notions Examples  LB norm le pow 1bb8f3f89542 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean#L98-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean#L98-L112

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

theorem P2M_Formalism_BasicNotions_Examples__LB_norm_le_pow_1bb8f3f89542 (g : G E Ω) (hg : g ∈ Dec (F := E) A) (z : Ω) (n : ℕ)
    (h : ‖j z‖ ≤ ‖((l : ℕ) : PadicAlgCl l)‖ ^ n) : ‖j (g z)‖ ≤ ‖((l : ℕ) : PadicAlgCl l)‖ ^ n := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«norm_le_pow» := P2M_Formalism_BasicNotions_Examples__LB_norm_le_pow_1bb8f3f89542
