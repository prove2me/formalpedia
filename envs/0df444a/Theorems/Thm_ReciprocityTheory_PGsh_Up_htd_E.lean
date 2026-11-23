-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_E
-- name    : ReciprocityTheory.PGsh.Up.htd_E
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:09.596087+00:00
-- url     : https://prove2.me/theorems/318bc8f1-e4f5-434c-89ff-95cc867c5ef2
-- title:
--   Up: htd E
-- statement:
--   The Up construction uses the htd E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L108-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L108-L119

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

theorem ReciprocityTheory.PGsh.Up.htd_E (H : HodgeTateDatum p g v R O σ cp) :
    (H.E.map (algebraMap ℤ_[p] R))ᵀ = -H.E.map (algebraMap ℤ_[p] R) ∧
    (∀ i, H.E.map (algebraMap ℤ_[p] R) i i = 0) ∧ IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := by sorry
