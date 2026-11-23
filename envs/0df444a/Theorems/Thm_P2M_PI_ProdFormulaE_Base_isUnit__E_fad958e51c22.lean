-- Prove2me | Theorems.Thm_P2M_PI_ProdFormulaE_Base_isUnit__E_fad958e51c22
-- name    : P2M_PI_ProdFormulaE_Base_isUnit__E_fad958e51c22
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:18:27.823936+00:00
-- url     : https://prove2.me/theorems/407a4490-9d8d-430e-9623-cc4c38824442
-- title:
--   P2 M PI Prod Formula E Base is Unit  E fad958e51c22: P2 M PI Prod Formula E Base is Unit  E fad958e51c22
-- statement:
--   The P2 M PI Prod Formula E Base is Unit  E fad958e51c22 construction uses the P2 M PI Prod Formula E Base is Unit  E fad958e51c22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean#L26-L27

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

theorem P2M_PI_ProdFormulaE_Base_isUnit__E_fad958e51c22 (L : LocAt F E sig p) {x : E} (hx : x ≠ 0) : IsUnit (L.ιE x) := by sorry

alias «PI».«ProdFormulaE».«Base».«isUnit_ιE» := P2M_PI_ProdFormulaE_Base_isUnit__E_fad958e51c22
