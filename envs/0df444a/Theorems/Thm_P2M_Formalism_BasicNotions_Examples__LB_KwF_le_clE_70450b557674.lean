-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_KwF_le_clE_70450b557674
-- name    : P2M_Formalism_BasicNotions_Examples__LB_KwF_le_clE_70450b557674
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:19.070801+00:00
-- url     : https://prove2.me/theorems/6c82f7c0-e9fc-452b-8e7d-105f31fc3493
-- title:
--   P2 M Formalism Basic Notions Examples  LB Kw F le cl E 70450b557674: P2 M Formalism Basic Notions Examples  LB Kw F le cl E 70450b557674
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB Kw F le cl E 70450b557674 construction uses the P2 M Formalism Basic Notions Examples  LB Kw F le cl E 70450b557674 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean#L44-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean#L44-L59

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

theorem P2M_Formalism_BasicNotions_Examples__LB_KwF_le_clE_70450b557674 : (KwF (E := E) j : Set (PadicAlgCl l)) ⊆
    closure (Set.range fun x : E => j (algebraMap E Ω x)) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«KwF_le_clE» := P2M_Formalism_BasicNotions_Examples__LB_KwF_le_clE_70450b557674
