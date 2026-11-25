-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_algebraMap_mem_clE_52b103178853
-- name    : P2M_Formalism_BasicNotions_Examples__LB_algebraMap_mem_clE_52b103178853
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:27.645973+00:00
-- url     : https://prove2.me/theorems/5114929c-0ac1-405c-85ae-1b356df7ee65
-- title:
--   P2 M Formalism Basic Notions Examples  LB algebra Map mem cl E 52b103178853: P2 M Formalism Basic Notions Examples  LB algebra Map mem cl E 52b103178853
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB algebra Map mem cl E 52b103178853 construction uses the P2 M Formalism Basic Notions Examples  LB algebra Map mem cl E 52b103178853 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean#L28-L42

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
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
  (j : Ω →+* PadicAlgCl l)

theorem P2M_Formalism_BasicNotions_Examples__LB_algebraMap_mem_clE_52b103178853 (x : ℚ_[l]) : algebraMap ℚ_[l] (PadicAlgCl l) x ∈ clE (E := E) j := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«algebraMap_mem_clE» := P2M_Formalism_BasicNotions_Examples__LB_algebraMap_mem_clE_52b103178853
