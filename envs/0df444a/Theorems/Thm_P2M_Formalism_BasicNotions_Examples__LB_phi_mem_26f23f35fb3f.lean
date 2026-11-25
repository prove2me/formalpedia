-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_phi_mem_26f23f35fb3f
-- name    : P2M_Formalism_BasicNotions_Examples__LB_phi_mem_26f23f35fb3f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:45:10.009401+00:00
-- url     : https://prove2.me/theorems/ee2f9ff0-728a-51f5-a5a8-56c75954ca29
-- title:
--   P2 M Formalism Basic Notions Examples  LB phi mem 26f23f35fb3f: P2 M Formalism Basic Notions Examples  LB phi mem 26f23f35fb3f
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB phi mem 26f23f35fb3f construction uses the P2 M Formalism Basic Notions Examples  LB phi mem 26f23f35fb3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean#L21-L31

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
variable {F : Type} [Field F] [NumberField F]

theorem P2M_Formalism_BasicNotions_Examples__LB_phi_mem_26f23f35fb3f (φ : F →+* PadicAlgCl l) (x : F) : φ x ∈ Kphi φ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«phi_mem» := P2M_Formalism_BasicNotions_Examples__LB_phi_mem_26f23f35fb3f
