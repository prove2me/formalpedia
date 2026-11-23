-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrobOn_eqOn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.eqOn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:34.70619+00:00
-- url     : https://prove2.me/theorems/412afc3d-170a-483a-b865-14700ebc2217
-- title:
--   Is Frob On: eq On
-- statement:
--   The Is Frob On construction uses the eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L121-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L121-L125

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.eqOn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ ψ : GK p K}
    (hφ : IsFrobOn p K n φ) (hψ : IsFrobOn p K n ψ) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) :
    φ x = ψ x := by sorry
