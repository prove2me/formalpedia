-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Top_clause2
-- name    : PI.ProdFormulaE.Top.clause2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:36:37.848345+00:00
-- url     : https://prove2.me/theorems/b080cd65-e77e-45bb-a639-32678a86108e
-- title:
--   Top: clause2
-- statement:
--   The Top construction uses the clause2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ProdFormulaEOf.lean#L108-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ProdFormulaEOf.lean#L108-L174

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

theorem PI.ProdFormulaE.Top.clause2 (hT : Tr.TrSum) (hI : St.TrInt) (hR : St.ResCharIff) (h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (x : E) :
    (Function.mulSupport fun p => (L p).psiE ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (L p).psiE ((L p).ιE x) =
        Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))) := by sorry
