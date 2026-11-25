-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_isAlgClosureQ_74b0853cbd95
-- name    : P2M_Formalism_BasicNotions_Examples__LB_isAlgClosureQ_74b0853cbd95
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:33:09.433131+00:00
-- url     : https://prove2.me/theorems/0f1e00de-a42a-4e87-b8ce-24ce58455225
-- title:
--   P2 M Formalism Basic Notions Examples  LB is Alg Closure Q 74b0853cbd95: P2 M Formalism Basic Notions Examples  LB is Alg Closure Q 74b0853cbd95
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB is Alg Closure Q 74b0853cbd95 construction uses the P2 M Formalism Basic Notions Examples  LB is Alg Closure Q 74b0853cbd95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocC.lean#L15-L18

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
omit hl
variable (E Ω)
include E

theorem P2M_Formalism_BasicNotions_Examples__LB_isAlgClosureQ_74b0853cbd95 : IsAlgClosure ℚ Ω := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«isAlgClosureQ» := P2M_Formalism_BasicNotions_Examples__LB_isAlgClosureQ_74b0853cbd95
