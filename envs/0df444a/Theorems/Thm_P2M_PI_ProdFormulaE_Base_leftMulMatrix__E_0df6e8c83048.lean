-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Base_leftMulMatrix__E_0df6e8c83048
-- name    : P2M_PI_ProdFormulaE_Base_leftMulMatrix__E_0df6e8c83048
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:56.052981+00:00
-- url     : https://prove2.me/theorems/62fbf6b1-f0c3-4da9-ba57-7f99aa4adc97
-- title:
--   P2 M PI Prod Formula E Base left Mul Matrix  E 0df6e8c83048: P2 M PI Prod Formula E Base left Mul Matrix  E 0df6e8c83048
-- statement:
--   The P2 M PI Prod Formula E Base left Mul Matrix  E 0df6e8c83048 construction uses the P2 M PI Prod Formula E Base left Mul Matrix  E 0df6e8c83048 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L63-L68

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

theorem P2M_PI_ProdFormulaE_Base_leftMulMatrix__E_0df6e8c83048 (L : LocAt F E sig p) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F E) (h : Module.finrank F E = 2) (x : E) :
    Algebra.leftMulMatrix (basisE L b h) (L.ιE x) = (Algebra.leftMulMatrix b x).map L.ιF := by sorry

alias «PI».«ProdFormulaE».«Base».«leftMulMatrix_ιE» := P2M_PI_ProdFormulaE_Base_leftMulMatrix__E_0df6e8c83048
