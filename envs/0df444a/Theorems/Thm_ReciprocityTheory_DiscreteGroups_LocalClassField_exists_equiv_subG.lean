-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_equiv_subG
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.exists_equiv_subG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:02.964284+00:00
-- url     : https://prove2.me/theorems/7dd72d1d-acee-4bc1-8998-9f081322b829
-- title:
--   Local Class Field: exists equiv sub G
-- statement:
--   The Local Class Field construction uses the exists equiv sub G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L172-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L172-L184

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.exists_equiv_subG (h : K ≤ L) : ∃ e : GK p L ≃* subG p K L, (∀ σ, (e σ : GK p K) = resGK h σ) ∧
    Continuous e ∧ Continuous e.symm := by sorry
