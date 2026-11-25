-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_rho
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.uval_rho
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:58.347151+00:00
-- url     : https://prove2.me/theorems/cfc42f1e-ebc2-567e-ab0b-35440b289935
-- title:
--   Local Class Field: uval rho
-- statement:
--   The Local Class Field construction uses the uval rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandF.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnitsHerbrandF.lean#L33-L34

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.uval_rho (σ : GK p K) (w : (layerU p K L).V) :
    uval ((layerU p K L).rho (QuotientGroup.mk σ) w) = σ (uval w) := by sorry
