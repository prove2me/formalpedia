-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Base_psiE__E_d316781c1d77
-- name    : P2M_PI_ProdFormulaE_Base_psiE__E_d316781c1d77
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:11.050199+00:00
-- url     : https://prove2.me/theorems/349e8f0c-0581-4710-bd3e-c52a23db9186
-- title:
--   P2 M PI Prod Formula E Base psi E  E d316781c1d77: P2 M PI Prod Formula E Base psi E  E d316781c1d77
-- statement:
--   The P2 M PI Prod Formula E Base psi E  E d316781c1d77 construction uses the P2 M PI Prod Formula E Base psi E  E d316781c1d77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L109-L115

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

theorem P2M_PI_ProdFormulaE_Base_psiE__E_d316781c1d77 (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    haveI := L.ellPrime
    ∃ a : ℚ, (∃ n : ℕ, a.den = (resChar p) ^ n) ∧
      ‖Algebra.trace ℚ_[resChar p] L.Fp (L.ιF (Algebra.trace F E x)) - (a : ℚ_[resChar p])‖ ≤ 1 ∧
      L.psiE (L.ιE x) = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) := by sorry

alias «PI».«ProdFormulaE».«Base».«psiE_ιE» := P2M_PI_ProdFormulaE_Base_psiE__E_d316781c1d77
