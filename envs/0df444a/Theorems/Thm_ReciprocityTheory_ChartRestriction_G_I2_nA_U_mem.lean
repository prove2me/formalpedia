-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_U_mem
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_U_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:55.789355+00:00
-- url     : https://prove2.me/theorems/34fbb902-ceb1-4bee-9cfd-bcc48cbdd896
-- title:
--   I2: n A U mem
-- statement:
--   The I2 construction uses the n A U mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L202-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L202-L232

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_U_mem {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n)
    {b : Fin n → Vsp X.dim} (hb : ∀ k, (q : ℂ) • b k ∈ X.L) : X.U q b F ∈ X.Sec q n := by sorry
