-- Prove2me | Theorems.Thm_PI_ProdFormulaE_Tr_exists_eq_ell_mul
-- name    : PI.ProdFormulaE.Tr.exists_eq_ell_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:36:15.418853+00:00
-- url     : https://prove2.me/theorems/cb779bda-1ec0-5846-b2ee-b9233c298935
-- title:
--   Tr: exists eq ell mul
-- statement:
--   The Tr construction uses the exists eq ell mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ExistsEqEllMul.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ExistsEqEllMul.lean#L9-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr

theorem PI.ProdFormulaE.Tr.exists_eq_ell_mul {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (X : 𝓞 F)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal →
      v.valuation F (X : F) ≤ v.valuation F (ℓ : F)) :
    ∃ Z : 𝓞 F, X = ℓ * Z := by sorry
