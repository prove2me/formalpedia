-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_exists_embAt_8f0e67d1d296
-- name    : P2M_Formalism_BasicNotions_Examples__LB_exists_embAt_8f0e67d1d296
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:41:38.210819+00:00
-- url     : https://prove2.me/theorems/ae158bd8-a512-4504-9c70-eb29bbc3041e
-- title:
--   P2 M Formalism Basic Notions Examples  LB exists emb At 8f0e67d1d296: P2 M Formalism Basic Notions Examples  LB exists emb At 8f0e67d1d296
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB exists emb At 8f0e67d1d296 construction uses the P2 M Formalism Basic Notions Examples  LB exists emb At 8f0e67d1d296 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean#L60-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean#L60-L69

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

theorem P2M_Formalism_BasicNotions_Examples__LB_exists_embAt_8f0e67d1d296 (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ φ : F →+* PadicAlgCl l, ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖φ (x : F)‖ < 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«exists_embAt» := P2M_Formalism_BasicNotions_Examples__LB_exists_embAt_8f0e67d1d296
