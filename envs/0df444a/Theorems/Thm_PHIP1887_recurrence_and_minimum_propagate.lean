-- Prove2me | Theorems.Thm_PHIP1887_recurrence_and_minimum_propagate
-- name    : PHIP1887.recurrence_and_minimum_propagate
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:44:40.847398+00:00
-- url     : https://prove2.me/theorems/3362ccf9-dc9a-4671-a5e9-bf0deef25d16
-- title:
--   recurrence and minimum propagate — PHIP1887
-- statement:
--   Sejam Q(k,x) e C(k,x) funções reais para k natural e x real. Para todo k≥1,x>0, suponha C(k,x)=k²Q(k,x)−2k(2k+1)Q(k+1,x). Suponha também que a existência de um valor negativo no andar k implique a existência de x>0 com Q(k,x)<0 e C(k,x)≥0. Então a existência de um valor negativo em k implica a existência de um valor negativo em k+1. A recorrência e a testemunha de curvatura são hipóteses; o lema não prova sua realização analítica.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.1; 166.2; 166.12; 167.7. Declaração PHIP1887.recurrence_and_minimum_propagate; arquivo lean/PHIP1887.lean; SHA-256 7c7571d1495047417c09bb8b5cea6bfe4beeabb916c533685af5e5731b864b6e. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e815bba24d5e67b9ec0f9

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
import Theorems.Thm_PHIP1887_central_negative_step
open MeasureTheory Set
open PHIP1887

theorem PHIP1887.recurrence_and_minimum_propagate (Q curvature : ℕ → ℝ → ℝ)
    (hrec : ∀ k x, 1 ≤ k → 0 < x →
      curvature k x = (k:ℝ)^2 * Q k x -
        2*(k:ℝ)*(2*(k:ℝ)+1)*Q (k+1) x)
    (hmin : ∀ k, 1 ≤ k → NegativeAt Q k →
      ∃ x, 0 < x ∧ Q k x < 0 ∧ 0 ≤ curvature k x) :
    ∀ k, 1 ≤ k → NegativeAt Q k → NegativeAt Q (k+1) := by sorry
