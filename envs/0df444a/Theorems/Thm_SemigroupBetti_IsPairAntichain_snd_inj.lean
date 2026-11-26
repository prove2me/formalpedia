-- Prove2me | Theorems.Thm_SemigroupBetti_IsPairAntichain_snd_inj
-- name    : SemigroupBetti.IsPairAntichain.snd_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:03:25.553733+00:00
-- url     : https://prove2.me/theorems/0c747b0f-c442-5632-95fb-282a13389f18
-- title:
--   Is Pair Antichain: snd inj
-- statement:
--   The Is Pair Antichain construction uses the snd inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L38-L42
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L38-L42

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
variable {T : Finset (ℕ × ℕ)}

theorem SemigroupBetti.IsPairAntichain.snd_inj (hT : IsPairAntichain T) {x y : ℕ × ℕ} (hx : x ∈ T) (hy : y ∈ T)
    (h : x.2 = y.2) : x = y := by sorry
