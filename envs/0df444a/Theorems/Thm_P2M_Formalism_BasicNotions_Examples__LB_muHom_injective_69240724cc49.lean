-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_muHom_injective_69240724cc49
-- name    : P2M_Formalism_BasicNotions_Examples__LB_muHom_injective_69240724cc49
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:40:50.157163+00:00
-- url     : https://prove2.me/theorems/01c3a1f3-2a50-4c91-b241-83e41e9d4ab4
-- title:
--   P2 M Formalism Basic Notions Examples  LB mu Hom injective 69240724cc49: P2 M Formalism Basic Notions Examples  LB mu Hom injective 69240724cc49
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB mu Hom injective 69240724cc49 construction uses the P2 M Formalism Basic Notions Examples  LB mu Hom injective 69240724cc49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean#L120-L126

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocG
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
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime]
variable (LL : FinExt l) {N : ℕ} [NeZero N] {ζ : PadicAlgCl l} (hζ : IsPrimitiveRoot ζ N) (hm : ζ ∈ LL.1)

theorem P2M_Formalism_BasicNotions_Examples__LB_muHom_injective_69240724cc49 : Function.Injective (muHom LL hζ hm) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«muHom_injective» := P2M_Formalism_BasicNotions_Examples__LB_muHom_injective_69240724cc49
