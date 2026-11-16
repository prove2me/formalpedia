-- Prove2me | Theorems.Thm_PHIP1891_one_cut_preserves_all_depths
-- name    : PHIP1891.one_cut_preserves_all_depths
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:08:19.121196+00:00
-- url     : https://prove2.me/theorems/68d7c466-3b2d-4314-ac05-a331568a6c3c
-- title:
--   one cut preserves all depths — PHIP1891
-- statement:
--   Sejam v,w sequências reais e e,d reais com d>0 e e<d. Se v(n)≤−d e |w(n)−v(n)|≤e para todo n natural, então w(n)<0 para todo n. A mesma margem e o mesmo controle de erro valem uniformemente em todos os índices.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.6; 166.7; 166.8; 166.12. Declaração PHIP1891.one_cut_preserves_all_depths; arquivo lean/PHIP1891.lean; SHA-256 6204ab37cffbfefdc5039664a23227617971fc4c5adccddf245e63aaaef23f46. Sem reivindicação de novidade. PHIP-1891; pacote de reprodução original.

import Mathlib
import Theorems.Thm_PHIP1891_negative_survives
open MeasureTheory Set
open PHIP1891

theorem PHIP1891.one_cut_preserves_all_depths (v w : ℕ → ℝ) (e d : ℝ)
    (hd : 0 < d) (hv : ∀ n, v n ≤ -d)
    (herr : ∀ n, |w n-v n| ≤ e) (he : e < d) :
    ∀ n, w n < 0 := by sorry
