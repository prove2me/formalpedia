-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCF_classGroup_hom_ext
-- name    : ReciprocityTheory.Neutral.Bridge.HCF.classGroup_hom_ext
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:15.831326+00:00
-- url     : https://prove2.me/theorems/47416dd9-a372-40c9-a243-62b3725620e5
-- title:
--   HCF: class Group hom ext
-- statement:
--   The HCF construction uses the class Group hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HilbertClassFieldA.lean#L42-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HilbertClassFieldA.lean#L42-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCF
variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

theorem ReciprocityTheory.Neutral.Bridge.HCF.classGroup_hom_ext {G : Type*} [Monoid G] (f₁ f₂ : ClassGroup R →* G)
    (h : ∀ v : HeightOneSpectrum R, f₁ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) =
      f₂ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) : f₁ = f₂ := by sorry
