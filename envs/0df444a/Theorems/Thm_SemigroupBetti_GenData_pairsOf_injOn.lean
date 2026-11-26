-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_pairsOf_injOn
-- name    : SemigroupBetti.GenData.pairsOf_injOn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:04:37.870137+00:00
-- url     : https://prove2.me/theorems/6172f99e-5c85-54e7-be02-4e192b695e75
-- title:
--   Gen Data: pairs Of inj On
-- statement:
--   The Gen Data construction uses the pairs Of inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L45-L54
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L45-L54

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

theorem SemigroupBetti.GenData.pairsOf_injOn {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) :
    Set.InjOn (fun d => (G.sel d K i, G.sel d K k)) F := by sorry
