-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Base_trace_tower
-- name    : PI.ProdFormulaE.Base.trace_tower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:16.146749+00:00
-- url     : https://prove2.me/theorems/24c28441-4733-4129-97a5-5abef7f779c1
-- title:
--   Base: trace tower
-- statement:
--   The Base construction uses the trace tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L86-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L86-L99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.ProdFormulaE PI.ProdFormulaE.Base
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem PI.ProdFormulaE.Base.trace_tower (L : LocAt F E sig p) (y : L.Ep) :
    (haveI := L.ellPrime
     letI := ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
     Algebra.trace ℚ_[resChar p] L.Ep y) =
    (haveI := L.ellPrime
     Algebra.trace ℚ_[resChar p] L.Fp (Algebra.trace L.Fp L.Ep y)) := by sorry
