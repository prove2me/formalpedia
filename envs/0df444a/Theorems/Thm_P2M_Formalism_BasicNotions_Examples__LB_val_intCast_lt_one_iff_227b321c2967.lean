-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_val_intCast_lt_one_iff_227b321c2967
-- name    : P2M_Formalism_BasicNotions_Examples__LB_val_intCast_lt_one_iff_227b321c2967
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:44.771991+00:00
-- url     : https://prove2.me/theorems/447b1459-8837-4dde-8452-e11dbe286ad1
-- title:
--   P2 M Formalism Basic Notions Examples  LB val int Cast lt one iff 227b321c2967: P2 M Formalism Basic Notions Examples  LB val int Cast lt one iff 227b321c2967
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB val int Cast lt one iff 227b321c2967 construction uses the P2 M Formalism Basic Notions Examples  LB val int Cast lt one iff 227b321c2967 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L99-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L99-L123

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

theorem P2M_Formalism_BasicNotions_Examples__LB_val_intCast_lt_one_iff_227b321c2967 (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«val_intCast_lt_one_iff» := P2M_Formalism_BasicNotions_Examples__LB_val_intCast_lt_one_iff_227b321c2967
