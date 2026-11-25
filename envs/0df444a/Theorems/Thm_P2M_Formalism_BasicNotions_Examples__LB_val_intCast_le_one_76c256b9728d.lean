-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_val_intCast_le_one_76c256b9728d
-- name    : P2M_Formalism_BasicNotions_Examples__LB_val_intCast_le_one_76c256b9728d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:35.538071+00:00
-- url     : https://prove2.me/theorems/9a719915-2f32-47ff-a0e1-2cbec1d63dbd
-- title:
--   P2 M Formalism Basic Notions Examples  LB val int Cast le one 76c256b9728d: P2 M Formalism Basic Notions Examples  LB val int Cast le one 76c256b9728d
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB val int Cast le one 76c256b9728d construction uses the P2 M Formalism Basic Notions Examples  LB val int Cast le one 76c256b9728d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L95-L97

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

theorem P2M_Formalism_BasicNotions_Examples__LB_val_intCast_le_one_76c256b9728d (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«val_intCast_le_one» := P2M_Formalism_BasicNotions_Examples__LB_val_intCast_le_one_76c256b9728d
