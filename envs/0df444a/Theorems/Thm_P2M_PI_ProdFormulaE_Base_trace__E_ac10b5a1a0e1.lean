-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Base_trace__E_ac10b5a1a0e1
-- name    : P2M_PI_ProdFormulaE_Base_trace__E_ac10b5a1a0e1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:02.942448+00:00
-- url     : https://prove2.me/theorems/b08018f3-b70f-42a8-915a-2ade899dfc70
-- title:
--   P2 M PI Prod Formula E Base trace  E ac10b5a1a0e1: P2 M PI Prod Formula E Base trace  E ac10b5a1a0e1
-- statement:
--   The P2 M PI Prod Formula E Base trace  E ac10b5a1a0e1 construction uses the P2 M PI Prod Formula E Base trace  E ac10b5a1a0e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L70-L76

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

theorem P2M_PI_ProdFormulaE_Base_trace__E_ac10b5a1a0e1 (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    Algebra.trace L.Fp L.Ep (L.ιE x) = L.ιF (Algebra.trace F E x) := by sorry

alias «PI».«ProdFormulaE».«Base».«trace_ιE» := P2M_PI_ProdFormulaE_Base_trace__E_ac10b5a1a0e1
