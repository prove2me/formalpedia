-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sel_coord_injOn
-- name    : SemigroupBetti.GenData.sel_coord_injOn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:57:42.337906+00:00
-- url     : https://prove2.me/theorems/2df334de-1afd-5836-aef3-c700b1ab30af
-- title:
--   Gen Data: sel coord inj On
-- statement:
--   Two selected vectors on a pair side `K = {i, k}` with equal `k`-coordinates come from the same
--   degree (Lemma 7 plus totality of `≤` on the `i`-coordinate).
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L132-L150
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L132-L150

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.sel_coord_injOn {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) :
    Set.InjOn (fun d => G.sel d K k) F := by sorry
