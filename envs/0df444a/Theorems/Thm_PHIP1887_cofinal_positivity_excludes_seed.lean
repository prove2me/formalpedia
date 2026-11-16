-- Prove2me | Theorems.Thm_PHIP1887_cofinal_positivity_excludes_seed
-- name    : PHIP1887.cofinal_positivity_excludes_seed
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:50:52.447414+00:00
-- url     : https://prove2.me/theorems/6fd86ec4-f5fa-46ef-9012-7d014b2ddd85
-- title:
--   cofinal positivity excludes seed — PHIP1887
-- statement:
--   Seja S um conjunto cofinal de naturais e Q uma família real. Suponha Q(k,x)≥0 para todo k∈S e x>0, e que a existência de um valor negativo se propague de k para k+1 para k≥1. Então não existe semente negativa em nenhum K≥1. Cofinal significa que S contém índices arbitrariamente grandes.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.1; 166.2; 166.12; 167.7. Declaração PHIP1887.cofinal_positivity_excludes_seed; arquivo lean/PHIP1887.lean; SHA-256 7c7571d1495047417c09bb8b5cea6bfe4beeabb916c533685af5e5731b864b6e. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e815bba24d5e67b9ec0f9

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
import Theorems.Thm_PHIP1887_negative_tail
open MeasureTheory Set
open PHIP1887

theorem PHIP1887.cofinal_positivity_excludes_seed (Q : ℕ → ℝ → ℝ) (S : Set ℕ)
    (hS : Cofinal S)
    (hpos : ∀ k ∈ S, PositiveAt Q k)
    (hstep : ∀ k, 1 ≤ k → NegativeAt Q k → NegativeAt Q (k+1)) :
    ¬ ∃ K, 1 ≤ K ∧ NegativeAt Q K := by sorry
