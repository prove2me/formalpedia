-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_resPair_factor
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.exists_resPair_factor
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:53:26.039649+00:00
-- url     : https://prove2.me/theorems/6d86226b-23c6-5e13-addd-b69bee48d636
-- title:
--   Local Class Field: exists res Pair factor
-- statement:
--   The Local Class Field construction uses the exists res Pair factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L264-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean#L264-L303

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.exists_resPair_factor (h : K ≤ L) :
    ∃ e : Pair ((kbarT p K).resSub (subG p K L)) (kbarT p L), (∀ n, Bijective (e.hom.H n)) ∧
      ∀ n x, (resPair h).hom.H n x =
        e.hom.H n ((Pair.res (kbarT p K) (subG p K L).subtype continuous_subtype_val).hom.H n x) := by sorry
