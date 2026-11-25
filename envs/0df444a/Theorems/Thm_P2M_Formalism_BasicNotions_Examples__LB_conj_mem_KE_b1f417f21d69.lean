-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_conj_mem_KE_b1f417f21d69
-- name    : P2M_Formalism_BasicNotions_Examples__LB_conj_mem_KE_b1f417f21d69
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T16:41:46.413875+00:00
-- url     : https://prove2.me/theorems/540d1765-22c2-4968-a053-68e2714bad7b
-- title:
--   P2 M Formalism Basic Notions Examples  LB conj mem KE b1f417f21d69: P2 M Formalism Basic Notions Examples  LB conj mem KE b1f417f21d69
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB conj mem KE b1f417f21d69 construction uses the P2 M Formalism Basic Notions Examples  LB conj mem KE b1f417f21d69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean#L42-L58

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

theorem P2M_Formalism_BasicNotions_Examples__LB_conj_mem_KE_b1f417f21d69 (φ : F →+* PadicAlgCl l) (τ : ↥(Kphi φ) →ₐ[ℚ_[l]] PadicAlgCl l) (y : ↥(Kphi φ)) :
    τ y ∈ KE l F := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«conj_mem_KE» := P2M_Formalism_BasicNotions_Examples__LB_conj_mem_KE_b1f417f21d69
