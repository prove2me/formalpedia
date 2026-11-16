-- Prove2me | Theorems.Thm_PHIP1886_folga_quadratica
-- name    : PHIP1886.folga_quadratica
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:00:59.741196+00:00
-- url     : https://prove2.me/theorems/b1a25a12-85c4-448d-97af-5c222abd531a
-- title:
--   folga quadratica — PHIP1886
-- statement:
--   Para s,T inteiros, s²+T²−2Ts=(s−T)².
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§165.6;166.1;167.8. Declaração PHIP1886.folga_quadratica; arquivo PHIP1886.lean; SHA-256 52323011b7b43e6c5010035258a3de098246675f7703bb7f8d1627df46bfd66c. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e81ea9b87c905305c280d

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem PHIP1886.folga_quadratica (s T : Int) : s * s + T * T - 2 * T * s = (s - T) ^ 2 := by sorry
