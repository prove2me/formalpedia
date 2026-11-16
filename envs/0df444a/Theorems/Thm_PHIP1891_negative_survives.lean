-- Prove2me | Theorems.Thm_PHIP1891_negative_survives
-- name    : PHIP1891.negative_survives
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:49:41.726147+00:00
-- url     : https://prove2.me/theorems/184f80d7-a185-400f-9de0-e84bbec167e4
-- title:
--   negative survives — PHIP1891
-- statement:
--   Se v,w,e,d são reais, d>0, v≤−d, |w−v|≤e e e<d, então w<0. A perturbação é menor que a margem negativa.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§166.6; 166.7; 166.8; 166.12. Declaração PHIP1891.negative_survives; arquivo lean/PHIP1891.lean; SHA-256 6204ab37cffbfefdc5039664a23227617971fc4c5adccddf245e63aaaef23f46. Sem reivindicação de novidade. PHIP-1891; pacote de reprodução original.

import Mathlib
open MeasureTheory Set

theorem PHIP1891.negative_survives (v w e d : ℝ)
    (hd : 0 < d) (hv : v ≤ -d) (herr : |w-v| ≤ e)
    (he : e < d) : w < 0 := by sorry
