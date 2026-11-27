-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PeriodRowsCompare_modelsEquiv___da8a0362d520
-- name    : P2M_GlobalTheory_PeriodRowsCompare_modelsEquiv___da8a0362d520
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:56.14048+00:00
-- url     : https://prove2.me/theorems/33686f80-a6bb-590f-8240-195bc86c7947
-- title:
--   P2 M Global Theory Period Rows Compare models Equiv   da8a0362d520: P2 M Global Theory Period Rows Compare models Equiv   da8a0362d520
-- statement:
--   The P2 M Global Theory Period Rows Compare models Equiv   da8a0362d520 construction uses the P2 M Global Theory Period Rows Compare models Equiv   da8a0362d520 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ModelBaseTrivModels.lean#L51-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ModelBaseTrivModels.lean#L51-L51

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ModelFamilies
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ModelBaseTrivModels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodRowsCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)} {F : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.FamAt Xo c σ e} {r : ℕ}

theorem P2M_GlobalTheory_PeriodRowsCompare_modelsEquiv___da8a0362d520 (M : Rows.ModelsOf F r) : (modelsEquiv F r M).φ = M.φ := by sorry

alias «GlobalTheory».«PeriodRowsCompare».«modelsEquiv_φ» := P2M_GlobalTheory_PeriodRowsCompare_modelsEquiv___da8a0362d520
