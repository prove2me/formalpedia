-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_btP_facts
-- name    : ReciprocityTheory.PGsh.Up.btP_facts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:16.014094+00:00
-- url     : https://prove2.me/theorems/76c43ae6-b8ff-4e21-a58e-e51af6e5e762
-- title:
--   Up: bt P facts
-- statement:
--   The Up construction uses the bt P facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/StdJForm4.lean#L15-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/StdJForm4.lean#L15-L100

import Definitions.Def_ReciprocityTheory_DualLattices_InvolutionPermApplyZero
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm4
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

theorem ReciprocityTheory.PGsh.Up.btP_facts (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (π : Equiv.Perm (Fin m)) (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hσ : ∀ i, σ (e i) = e (π i)) (hsT : (∑ i, H.ρ (e i)) + H.P = 1)
    (hPT : ∀ i, H.ρ (e i) * H.P = 0) (hsL : (∑ i, H.ρL (e i)) + H.PL = 1)
    (hPL : ∀ i, H.ρL (e i) * H.PL = 0) :
    (btP H e)ᵀ * H.Ht - H.Htᵀ * btP H e = cp • H.E.map (algebraMap ℤ_[p] R) ∧
    (∀ i, btP H e * (H.ρ (e i)).map (algebraMap ℤ_[p] R) = H.ρL (e i) * btP H e) ∧
    btP H e * H.P.map (algebraMap ℤ_[p] R) = H.PL * btP H e := by sorry
