-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_val_lt_one_iff_ff0494b5971d
-- name    : P2M_Formalism_BasicNotions_Examples__LB_val_lt_one_iff_ff0494b5971d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:44.797717+00:00
-- url     : https://prove2.me/theorems/044ede7a-4c62-40b6-928e-4ba634ad1718
-- title:
--   P2 M Formalism Basic Notions Examples  LB val lt one iff ff0494b5971d: P2 M Formalism Basic Notions Examples  LB val lt one iff ff0494b5971d
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB val lt one iff ff0494b5971d construction uses the P2 M Formalism Basic Notions Examples  LB val lt one iff ff0494b5971d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L64-L75

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

theorem P2M_Formalism_BasicNotions_Examples__LB_val_lt_one_iff_ff0494b5971d {A : ValuationSubring Ω} {j : Ω →+* PadicAlgCl l}
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (y : Ω) : A.valuation y < 1 ↔ ‖j y‖ < 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«val_lt_one_iff» := P2M_Formalism_BasicNotions_Examples__LB_val_lt_one_iff_ff0494b5971d
