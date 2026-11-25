-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrob_eqOn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrob.eqOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:15:21.971067+00:00
-- url     : https://prove2.me/theorems/8bf34900-bcd4-422a-b2ff-ba82426a6b2d
-- title:
--   Is Frob: eq On
-- statement:
--   The Is Frob construction uses the eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L147-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ExistsDvdQKPowSubOne.lean#L147-L149

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrobOn_eqOn

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
variable {p K}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrob.eqOn (hK : FiniteDimensional ℚ_[p] K) {σ τ : GK p K} (hσ : IsFrob p K σ) (hτ : IsFrob p K τ)
    {x : PadicAlgCl p} (hx : x ∈ MaximalUnramifiedExtension p K) : σ x = τ x := by sorry
