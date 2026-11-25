-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PeriodOnto_gram_eq__a7a60263ce08
-- name    : P2M_GlobalTheory_PeriodOnto_gram_eq__a7a60263ce08
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:21.711091+00:00
-- url     : https://prove2.me/theorems/88e74b26-69dc-4728-aad3-f15644112441
-- title:
--   P2 M Global Theory Period Onto gram eq  a7a60263ce08: P2 M Global Theory Period Onto gram eq  a7a60263ce08
-- statement:
--   The P2 M Global Theory Period Onto gram eq  a7a60263ce08 construction uses the P2 M Global Theory Period Onto gram eq  a7a60263ce08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L420-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L420-L425

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]

theorem P2M_GlobalTheory_PeriodOnto_gram_eq__a7a60263ce08 {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ G x = xᵀ * G.map τ * x.map conj := by sorry

alias «GlobalTheory».«PeriodOnto».«gram_eq'» := P2M_GlobalTheory_PeriodOnto_gram_eq__a7a60263ce08
