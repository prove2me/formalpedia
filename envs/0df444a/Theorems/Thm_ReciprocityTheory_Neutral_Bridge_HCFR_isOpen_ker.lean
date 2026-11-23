-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_isOpen_ker
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.isOpen_ker
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:41.091192+00:00
-- url     : https://prove2.me/theorems/dca0258d-9501-4e3f-822f-c3a33f1dada1
-- title:
--   HCFR: is Open ker
-- statement:
--   The HCFR construction uses the is Open ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L42-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L42-L73

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]

theorem ReciprocityTheory.Neutral.Bridge.HCFR.isOpen_ker (Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K)
    (hc : Continuous Art) (E : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K E) :
    IsOpen ((((abRestrict K E h).comp Art).comp (QuotientGroup.mk' (diagUnits K).range)).ker :
      Set (Ideles K)) := by sorry
