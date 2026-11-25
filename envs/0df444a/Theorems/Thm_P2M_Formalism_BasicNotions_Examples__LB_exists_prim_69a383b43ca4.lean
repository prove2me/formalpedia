-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_exists_prim_69a383b43ca4
-- name    : P2M_Formalism_BasicNotions_Examples__LB_exists_prim_69a383b43ca4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T16:48:57.737298+00:00
-- url     : https://prove2.me/theorems/fa96dd61-3e75-4322-ac13-66158c1f5109
-- title:
--   P2 M Formalism Basic Notions Examples  LB exists prim 69a383b43ca4: P2 M Formalism Basic Notions Examples  LB exists prim 69a383b43ca4
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB exists prim 69a383b43ca4 construction uses the P2 M Formalism Basic Notions Examples  LB exists prim 69a383b43ca4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean#L74-L81

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
variable (l)

theorem P2M_Formalism_BasicNotions_Examples__LB_exists_prim_69a383b43ca4 (N : ℕ) (hN : 0 < N) : ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ N := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«exists_prim» := P2M_Formalism_BasicNotions_Examples__LB_exists_prim_69a383b43ca4
