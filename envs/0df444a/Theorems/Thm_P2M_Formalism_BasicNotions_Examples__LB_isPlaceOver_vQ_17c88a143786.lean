-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_isPlaceOver_vQ_17c88a143786
-- name    : P2M_Formalism_BasicNotions_Examples__LB_isPlaceOver_vQ_17c88a143786
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:24.992018+00:00
-- url     : https://prove2.me/theorems/54e7943c-34a0-4909-bd95-8b9d93020277
-- title:
--   P2 M Formalism Basic Notions Examples  LB is Place Over v Q 17c88a143786: P2 M Formalism Basic Notions Examples  LB is Place Over v Q 17c88a143786
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB is Place Over v Q 17c88a143786 construction uses the P2 M Formalism Basic Notions Examples  LB is Place Over v Q 17c88a143786 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L125-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L125-L136

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

theorem P2M_Formalism_BasicNotions_Examples__LB_isPlaceOver_vQ_17c88a143786 [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«isPlaceOver_vQ» := P2M_Formalism_BasicNotions_Examples__LB_isPlaceOver_vQ_17c88a143786
