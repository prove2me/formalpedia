-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_intCast_mem_vQ_b647479a58db
-- name    : P2M_Formalism_BasicNotions_Examples__LB_intCast_mem_vQ_b647479a58db
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:26.976199+00:00
-- url     : https://prove2.me/theorems/2bf1b93f-f6de-4de9-8e35-4a84c432d544
-- title:
--   P2 M Formalism Basic Notions Examples  LB int Cast mem v Q b647479a58db: P2 M Formalism Basic Notions Examples  LB int Cast mem v Q b647479a58db
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB int Cast mem v Q b647479a58db construction uses the P2 M Formalism Basic Notions Examples  LB int Cast mem v Q b647479a58db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L90-L93

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
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
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise
variable (l : ℕ) [hl : Fact l.Prime]
variable {l} {Ω : Type} [Field Ω]

theorem P2M_Formalism_BasicNotions_Examples__LB_intCast_mem_vQ_b647479a58db (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«intCast_mem_vQ» := P2M_Formalism_BasicNotions_Examples__LB_intCast_mem_vQ_b647479a58db
