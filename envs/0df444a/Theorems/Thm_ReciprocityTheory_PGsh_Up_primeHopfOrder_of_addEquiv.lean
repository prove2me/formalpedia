-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_primeHopfOrder_of_addEquiv
-- name    : ReciprocityTheory.PGsh.Up.primeHopfOrder_of_addEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:20.72694+00:00
-- url     : https://prove2.me/theorems/92e0b9e5-ec0c-5c41-a906-0485c92088b5
-- title:
--   Up: prime Hopf Order of add Equiv
-- statement:
--   The Up construction uses the prime Hopf Order of add Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PrimeHopfOrderOfAddEquiv.lean#L122-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PrimeHopfOrderOfAddEquiv.lean#L122-L187

import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2

theorem ReciprocityTheory.PGsh.Up.primeHopfOrder_of_addEquiv (hU3 : PrimeHopfOrderStatement) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hv : v.Integers R) (hp : v (p : C) < 1) {K : Type} [AddCommGroup K] [Fintype K]
    [DecidableEq K] (e : ZMod p ≃+ K) (AK : HopfOrder (C := C) R K) :
    ∃ (xK : K → C) (δ : R) (x1 : C), xK ∈ augIdeal AK.carrier ∧
      xK ^ p = (fun a => algebraMap R C δ * xK a) ∧ v (algebraMap R C δ) = v x1 ^ (p - 1) ∧
      (∀ f ∈ augIdeal AK.carrier, ∃ r : R,
        f - r • xK ∈ augIdeal AK.carrier * augIdeal AK.carrier) ∧
      HasColen R v AK.carrier (v x1 ^ (p * (p - 1) / 2)) := by sorry
