-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_coeff_le_gauss_abs
-- name    : ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:19.5517+00:00
-- url     : https://prove2.me/theorems/54be6a23-b57d-401f-bcba-06b1504adaba
-- title:
--   Multiplicative Heights: coeff le gauss abs
-- statement:
--   The Multiplicative Heights construction uses the coeff le gauss abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L12-L20

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

theorem ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs (w : FinitePlace K) (f : MvPolynomial σ K) (s : σ →₀ ℕ) :
    w (f.coeff s) ≤ gaussAbs w f := by sorry
