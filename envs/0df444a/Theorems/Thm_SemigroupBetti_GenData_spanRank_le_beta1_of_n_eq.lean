-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_spanRank_le_beta1_of_n_eq
-- name    : SemigroupBetti.GenData.spanRank_le_beta1_of_n_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:53:00.7909+00:00
-- url     : https://prove2.me/theorems/80b35e84-2f90-46ad-a0ec-5c08bc710256
-- title:
--   Gen Data: span Rank le beta1 of n eq
-- statement:
--   The bridge for an arbitrary generator vector `n` equal to `G.n` (avoids rewriting `G.n`
--   under the dependent `G.beta1`). With `n` and `toricIdeal` from `Challenge.lean` this reads
--   `(toricIdeal K n).spanRank ≤ G.beta1` (definitional unfolding).
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L296-L300
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L296-L300

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

theorem SemigroupBetti.GenData.spanRank_le_beta1_of_n_eq {n : Fin 4 → ℕ} (hn : G.n = n) :
    (RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom).spanRank ≤
      (G.beta1 : Cardinal) := by sorry
