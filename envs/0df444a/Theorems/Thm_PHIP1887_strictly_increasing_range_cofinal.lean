-- Prove2me | Theorems.Thm_PHIP1887_strictly_increasing_range_cofinal
-- name    : PHIP1887.strictly_increasing_range_cofinal
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:44:59.560029+00:00
-- url     : https://prove2.me/theorems/5521ae19-11f5-4535-a80f-be9c6462e6e3
-- title:
--   strictly increasing range cofinal — PHIP1887
-- statement:
--   Se a é uma sequência de naturais com a(n)<a(n+1) para todo n, sua imagem é cofinal: para todo K há um índice da imagem maior ou igual a K.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.1; 166.2; 166.12; 167.7. Declaração PHIP1887.strictly_increasing_range_cofinal; arquivo lean/PHIP1887.lean; SHA-256 7c7571d1495047417c09bb8b5cea6bfe4beeabb916c533685af5e5731b864b6e. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e815bba24d5e67b9ec0f9

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
open MeasureTheory Set
open PHIP1887

theorem PHIP1887.strictly_increasing_range_cofinal (a : ℕ → ℕ)
    (h : ∀ n, a n < a (n+1)) : Cofinal (Set.range a) := by sorry
