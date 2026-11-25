-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_fracTensor_exists_den
-- name    : ReciprocityTheory.AnForm.R.BaseChangeC.fracTensor_exists_den
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:12.41773+00:00
-- url     : https://prove2.me/theorems/3329c7ee-957e-4a2a-8880-b26333d9ae1f
-- title:
--   Base Change C: frac Tensor exists den
-- statement:
--   The Base Change C construction uses the frac Tensor exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCA.lean#L13-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCA.lean#L13-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.BaseChangeC
open MvPolynomial TensorProduct
variable (ι : Type) (F : Type) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial ι ℚ) F]
  [IsScalarTower ℚ (MvPolynomial ι ℚ) F] [IsFractionRing (MvPolynomial ι ℚ) F]
  (C : Type) [Field C] [Algebra ℚ C]

theorem ReciprocityTheory.AnForm.R.BaseChangeC.fracTensor_exists_den (z : F ⊗[ℚ] C) :
    ∃ s ∈ nonZeroDivisors (MvPolynomial ι ℚ), ∃ w : MvPolynomial ι ℚ ⊗[ℚ] C,
      (algebraMap (MvPolynomial ι ℚ) F s ⊗ₜ[ℚ] (1 : C)) * z =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F)
          (AlgHom.id ℚ C) w := by sorry
