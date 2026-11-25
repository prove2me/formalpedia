-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_up_shift
-- name    : ReciprocityTheory.PGsh.Up.up_shift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:14:24.373383+00:00
-- url     : https://prove2.me/theorems/f7a31dfb-6e27-5c72-a042-9f06eba220bd
-- title:
--   Up: up shift
-- statement:
--   The Up construction uses the up shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LengthDegreeAbelianVariety.lean#L112-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LengthDegreeAbelianVariety.lean#L112-L156

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelsAgreeEquivariantly
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfWdetFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
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

theorem ReciprocityTheory.PGsh.Up.up_shift (hU7 : UnramifiedCokernelLengthStatement) (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R)
    (hp2 : p ≠ 2) (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (ρ r : ℕ) (rG : Fin U.m → ℕ)
    (hrB : ∀ j, U.r j + ρ = rG j) (hrc : (rG (U.cj i) : ℝ) = r - rG i)
    (N : Type) [AddCommGroup N] [Module R N] (E : cokE H.Ht U.εT U.εL i (U.cj i) ≃ₗ[R] N)
    (V1 : NNReal) (hN : HasLen v R N V1) :
    (v (algebraMap R C (p : R)) : ℝ) ^ ((rG i : ℝ) / (p - 1) -
      ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * rG ((U.φ ^ (n + 1)) i) +
      ((r : ℝ) - rG i - ρ) / (p - 1)) ≤ V1 := by sorry
