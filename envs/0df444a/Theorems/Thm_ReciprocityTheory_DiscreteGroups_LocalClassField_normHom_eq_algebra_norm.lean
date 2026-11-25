-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_eq_algebra_norm
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_eq_algebra_norm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:07.420586+00:00
-- url     : https://prove2.me/theorems/af9369d1-f636-461a-aaa5-d1f51b2d13bb
-- title:
--   Local Class Field: norm Hom eq algebra norm
-- statement:
--   The Local Class Field construction uses the norm Hom eq algebra norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L173-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L173-L203

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
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
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_eq_algebra_norm (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (y : KbarMult p)
    (hy : y ∈ multOf p L) :
    ((Additive.toMul (normHom p K L y) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ((Algebra.norm K (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ :
        IntermediateField.extendScalars h) : K) : PadicAlgCl p) := by sorry
