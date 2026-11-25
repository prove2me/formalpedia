-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Base_trace__E_ql_8c607bdd56d9
-- name    : P2M_PI_ProdFormulaE_Base_trace__E_ql_8c607bdd56d9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:28.328655+00:00
-- url     : https://prove2.me/theorems/c7bec86d-d827-4699-bfb6-35f6fbd351ba
-- title:
--   P2 M PI Prod Formula E Base trace  E ql 8c607bdd56d9: P2 M PI Prod Formula E Base trace  E ql 8c607bdd56d9
-- statement:
--   The P2 M PI Prod Formula E Base trace  E ql 8c607bdd56d9 construction uses the P2 M PI Prod Formula E Base trace  E ql 8c607bdd56d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L101-L107

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

theorem P2M_PI_ProdFormulaE_Base_trace__E_ql_8c607bdd56d9 (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    (haveI := L.ellPrime
     letI := ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
     Algebra.trace ℚ_[resChar p] L.Ep (L.ιE x)) =
    (haveI := L.ellPrime
     Algebra.trace ℚ_[resChar p] L.Fp (L.ιF (Algebra.trace F E x))) := by sorry

alias «PI».«ProdFormulaE».«Base».«trace_ιE_ql» := P2M_PI_ProdFormulaE_Base_trace__E_ql_8c607bdd56d9
