-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_vp_rpow
-- name    : ReciprocityTheory.PGsh.Up.vp_rpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:28:05.339103+00:00
-- url     : https://prove2.me/theorems/d067fe86-0c1a-4ec9-8c6a-eaf754f22ad3
-- title:
--   Up: vp rpow
-- statement:
--   The Up construction uses the vp rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L137-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLowerBoundOf.lean#L137-L156

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

theorem ReciprocityTheory.PGsh.Up.vp_rpow (hS : HodgeTateSetting p v R O σ cp) (d : ℕ) :
    (v (algebraMap R C (p : R)) : ℝ) ^ ((d : ℝ) / (p - 1)) =
      ((v (algebraMap R C cp) ^ d : NNReal) : ℝ) := by sorry
