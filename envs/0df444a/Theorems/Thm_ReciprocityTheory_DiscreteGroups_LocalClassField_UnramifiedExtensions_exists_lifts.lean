-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_lifts
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.exists_lifts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:46.373269+00:00
-- url     : https://prove2.me/theorems/ed169fef-0747-4b2c-8e98-009540624dad
-- title:
--   Unramified Extensions: exists lifts
-- statement:
--   The Unramified Extensions construction uses the exists lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L100-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean#L100-L120

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p} {K}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.exists_lifts {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) :
    ∃ f : ℕ, 0 < f ∧ qK p L = qK p K ^ f ∧ ∃ ω : Fin f → Obar p, (∀ j, (ω j : PadicAlgCl p) ∈ L) ∧
      LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i)) := by sorry
