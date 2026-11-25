-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_sum
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.uval_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:56:17.766391+00:00
-- url     : https://prove2.me/theorems/d853bf09-8787-4cdb-a14c-c2db43ca59cb
-- title:
--   Local Class Field: uval sum
-- statement:
--   The Local Class Field construction uses the uval sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandF.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandF.lean#L26-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
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
variable [(subG p K L).Normal]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.uval_sum {ι : Type*} (s : Finset ι) (f : ι → (layerU p K L).V) :
    uval (∑ i ∈ s, f i) = ∏ i ∈ s, uval (f i) := by sorry
