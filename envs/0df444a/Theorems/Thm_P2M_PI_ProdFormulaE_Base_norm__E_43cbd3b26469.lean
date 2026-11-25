-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Base_norm__E_43cbd3b26469
-- name    : P2M_PI_ProdFormulaE_Base_norm__E_43cbd3b26469
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:57:12.724096+00:00
-- url     : https://prove2.me/theorems/c4ae9ab9-cd29-4cb4-90ba-be8562a0f64b
-- title:
--   P2 M PI Prod Formula E Base norm  E 43cbd3b26469: P2 M PI Prod Formula E Base norm  E 43cbd3b26469
-- statement:
--   The P2 M PI Prod Formula E Base norm  E 43cbd3b26469 construction uses the P2 M PI Prod Formula E Base norm  E 43cbd3b26469 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L78-L84

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

theorem P2M_PI_ProdFormulaE_Base_norm__E_43cbd3b26469 (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    Algebra.norm L.Fp (L.ιE x) = L.ιF (Algebra.norm F x) := by sorry

alias «PI».«ProdFormulaE».«Base».«norm_ιE» := P2M_PI_ProdFormulaE_Base_norm__E_43cbd3b26469
