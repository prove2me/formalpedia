-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_exists_coord_eq
-- name    : SemigroupBetti.GenData.exists_coord_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:58:46.684087+00:00
-- url     : https://prove2.me/theorems/9797bdb1-577b-55aa-844c-9c6404a93edf
-- title:
--   Gen Data: exists coord eq
-- statement:
--   **Saturation.** If the selected `k`-coordinates of a family of size `c` take values in
--   `[1, c]`, every value in `[1, c]` is attained.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L82-L90
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L82-L90

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.exists_coord_eq {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k) (hKe : K = {i, k})
    (F : Finset ℕ) (hF : ∀ d ∈ F, G.IsSplit d K) {c : ℕ}
    (hc : ∀ d ∈ F, 1 ≤ G.sel d K k ∧ G.sel d K k ≤ c) (hcard : F.card = c) {v : ℕ}
    (hv1 : 1 ≤ v) (hvc : v ≤ c) : ∃ d ∈ F, G.sel d K k = v := by sorry
