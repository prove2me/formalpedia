-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sub_mem_of_sharesVar
-- name    : SemigroupBetti.GenData.sub_mem_of_sharesVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:25.205792+00:00
-- url     : https://prove2.me/theorems/28bb2575-c142-4b85-9b4f-95b22e4c773f
-- title:
--   Gen Data: sub mem of shares Var
-- statement:
--   Edge step (write-up Lemma 0C): if `z, z'` of degree `d` share a variable `i`, then
--   `X^z - X^{z'} = Xᵢ (X^{z-eᵢ} - X^{z'-eᵢ})`, and the inner binomial has degree `d - nᵢ < d`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L150-L167
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L150-L167

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

theorem SemigroupBetti.GenData.sub_mem_of_sharesVar {J : Ideal (MvPolynomial (Fin 4) K)} {d : ℕ}
    (IH : ∀ e < d, ∀ z z' : Fin 4 → ℕ, G.nu z = e → G.nu z' = e → mono K z - mono K z' ∈ J)
    {z z' : Fin 4 → ℕ} (hz : G.nu z = d) (hz' : G.nu z' = d) (h : SharesVar z z') :
    mono K z - mono K z' ∈ J := by sorry
