-- Prove2me | Theorems.Thm_PI_ProdFormulaE_modF_iota_finitePlace
-- name    : PI.ProdFormulaE.modF_iota_finitePlace
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:22.726473+00:00
-- url     : https://prove2.me/theorems/9424000f-9838-5b6e-986d-a496d44f0e0f
-- title:
--   Prod Formula E: mod F iota finite Place
-- statement:
--   The Prod Formula E construction uses the mod F iota finite Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ModFIotaFinitePlace.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ModFIotaFinitePlace.lean#L74-L79

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ModFIotaFinitePlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel IsDedekindDomain NumberField
open PI PI.ProdFormulaE

theorem PI.ProdFormulaE.modF_iota_finitePlace {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K) (hI : IndexFormula) (hC : CardStep) (hd : DenseRange ι)
    (hv : ∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) (z : F) :
    modF K (ι z) = FinitePlace.mk p z := by sorry
