-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_proj
-- name    : ReciprocityTheory.PGsh.Up.FrobeniusGroupField.proj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:38.169809+00:00
-- url     : https://prove2.me/theorems/65d88a49-d12b-4eeb-b5d9-d2a9d2aa91f3
-- title:
--   Frobenius Group Field: proj
-- statement:
--   The Frobenius Group Field construction uses the proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigPowEqOne.lean#L57-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigPowEqOne.lean#L57-L171

import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.FrobeniusGroupField.proj (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Type} [CommGroup G] [Fintype G] (hG : IsUnit (Fintype.card G : R))
    (A : G → Matrix n n ℤ_[p]) (hA : ∀ γ γ', A (γ * γ') = A γ * A γ') (hA1 : A 1 = 1)
    (εT : ι → Matrix n n R) (horth : ∀ i j, εT i * εT j = if i = j then εT i else 0)
    (hsum : ∑ i, εT i = 1) (ψ : ι → G → R)
    (heig : ∀ j γ, (A γ).map (algebraMap ℤ_[p] R) * εT j = ψ j γ • εT j)
    (hsep : ∀ j k, εT j ≠ 0 → εT k ≠ 0 → j ≠ k → ∃ γ, ψ j γ ≠ ψ k γ)
    (i : ι) (hi : εT i ≠ 0) : ∃ j, εT j ≠ 0 ∧ ∀ γ, ψ j γ = ψ i γ ^ p := by sorry
