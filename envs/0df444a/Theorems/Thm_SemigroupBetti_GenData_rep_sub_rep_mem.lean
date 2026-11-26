-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_rep_sub_rep_mem
-- name    : SemigroupBetti.GenData.rep_sub_rep_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:07.045881+00:00
-- url     : https://prove2.me/theorems/3445f85b-015b-53ec-b1e8-a7052dfcc9eb
-- title:
--   Gen Data: rep sub rep mem
-- statement:
--   Base-component step (write-up Lemma 0D/0F): the chosen binomials link any two
--   representatives at a degree `d ≤ H`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L182-L198
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L182-L198

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]

theorem SemigroupBetti.GenData.rep_sub_rep_mem {d : ℕ} (hd : d ≤ G.H) (C C' : (G.nabla d).ConnectedComponent) :
    mono K (G.rep C) - mono K (G.rep C') ∈ Ideal.span (G.binomGens K : Set _) := by sorry
