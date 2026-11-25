-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Top_clause1
-- name    : PI.ProdFormulaE.Top.clause1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:36:33.046276+00:00
-- url     : https://prove2.me/theorems/85e6274c-2706-4a2b-b98d-416fa10968e3
-- title:
--   Top: clause1
-- statement:
--   The Top construction uses the clause1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ProdFormulaEOf.lean#L36-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ProdFormulaEOf.lean#L36-L54

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

theorem PI.ProdFormulaE.Top.clause1 (hH : St.HaarAlg) (hN : St.NormLoc) (h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)
    (M : ∀ p, Model (L p).Fp (L p).Ep) (hM : ∀ p, (M p).OK) (x : E) (hx : x ≠ 0) :
    (Function.mulSupport fun p => (M p).modK ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((L p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹ := by sorry
