-- Prove2me | Theorems.Thm_PHIP1887_negative_tail
-- name    : PHIP1887.negative_tail
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:44:44.3785+00:00
-- url     : https://prove2.me/theorems/f291137b-f873-44d5-afcd-0f2fee1b2f00
-- title:
--   negative tail — PHIP1887
-- statement:
--   Se Q é uma família real e, para todo k≥1, a existência de x>0 com Q(k,x)<0 implica essa existência no andar k+1, então uma semente negativa em K≥1 implica uma semente negativa em cada k≥K. O ponto x pode variar com k.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.1; 166.2; 166.12; 167.7. Declaração PHIP1887.negative_tail; arquivo lean/PHIP1887.lean; SHA-256 7c7571d1495047417c09bb8b5cea6bfe4beeabb916c533685af5e5731b864b6e. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e815bba24d5e67b9ec0f9

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
open MeasureTheory Set
open PHIP1887

theorem PHIP1887.negative_tail (Q : ℕ → ℝ → ℝ)
    (hstep : ∀ k, 1 ≤ k → NegativeAt Q k → NegativeAt Q (k+1))
    (K : ℕ) (hK : 1 ≤ K) (hseed : NegativeAt Q K) :
    ∀ k, K ≤ k → NegativeAt Q k := by sorry
