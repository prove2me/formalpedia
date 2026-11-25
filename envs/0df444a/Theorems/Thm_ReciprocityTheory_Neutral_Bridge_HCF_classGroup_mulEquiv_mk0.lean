-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCF_classGroup_mulEquiv_mk0
-- name    : ReciprocityTheory.Neutral.Bridge.HCF.classGroup_mulEquiv_mk0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:02.711394+00:00
-- url     : https://prove2.me/theorems/34c355fe-4a52-5a9c-9aad-f9222e617e83
-- title:
--   HCF: class Group mul Equiv mk0
-- statement:
--   The HCF construction uses the class Group mul Equiv mk0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HilbertClassFieldA.lean#L17-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HilbertClassFieldA.lean#L17-L40

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

theorem ReciprocityTheory.Neutral.Bridge.HCF.classGroup_mulEquiv_mk0 (g : R ≃+* R') (I : (Ideal R)⁰) :
    ClassGroup.mulEquiv g (ClassGroup.mk0 I) = ClassGroup.mk0 ⟨(I : Ideal R).map g, map_mem_nzd g I⟩ := by sorry
