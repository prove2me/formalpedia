-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Top_modK_eq
-- name    : PI.ProdFormulaE.Top.modK_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:36:32.610663+00:00
-- url     : https://prove2.me/theorems/4d851aea-6bd9-4cf6-bf60-6a8f472d0873
-- title:
--   Top: mod K eq
-- statement:
--   The Top construction uses the mod K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ProdFormulaEOf.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ProdFormulaEOf.lean#L22-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ProdFormulaEOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc
open PI PI.ProdFormulaE PI.ProdFormulaE.Top
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem PI.ProdFormulaE.Top.modK_eq (hH : St.HaarAlg) (hN : St.NormLoc) (h2 : Module.finrank F E = 2)
    {p : HeightOneSpectrum (𝓞 F)} (L : LocAt F E sig p) (M : Model L.Fp L.Ep) (hM : M.OK)
    {x : E} (hx : x ≠ 0) :
    M.modK (L.ιE x) = FinitePlace.mk p (Algebra.norm F x) := by sorry
