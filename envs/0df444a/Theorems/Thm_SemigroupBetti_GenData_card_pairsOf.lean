-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_card_pairsOf
-- name    : SemigroupBetti.GenData.card_pairsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:05:45.590572+00:00
-- url     : https://prove2.me/theorems/5fbc9d28-7534-4082-bf9a-5073b34b42c8
-- title:
--   Gen Data: card pairs Of
-- statement:
--   The Gen Data construction uses the card pairs Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L56-L58
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L56-L58

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

theorem SemigroupBetti.GenData.card_pairsOf {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) : (G.pairsOf F K i k).card = F.card := by sorry
