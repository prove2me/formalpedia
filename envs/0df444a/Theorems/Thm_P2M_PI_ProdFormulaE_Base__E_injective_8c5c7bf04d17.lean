-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Base__E_injective_8c5c7bf04d17
-- name    : P2M_PI_ProdFormulaE_Base__E_injective_8c5c7bf04d17
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:54.177218+00:00
-- url     : https://prove2.me/theorems/3689277e-5b79-58fc-bd0f-734607620ea4
-- title:
--   P2 M PI Prod Formula E Base  E injective 8c5c7bf04d17: P2 M PI Prod Formula E Base  E injective 8c5c7bf04d17
-- statement:
--   The P2 M PI Prod Formula E Base  E injective 8c5c7bf04d17 construction uses the P2 M PI Prod Formula E Base  E injective 8c5c7bf04d17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L22-L24

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

theorem P2M_PI_ProdFormulaE_Base__E_injective_8c5c7bf04d17 (L : LocAt F E sig p) : Function.Injective L.ιE := by sorry

alias «PI».«ProdFormulaE».«Base».«ιE_injective» := P2M_PI_ProdFormulaE_Base__E_injective_8c5c7bf04d17
