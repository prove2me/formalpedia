-- Prove2me | Theorems.Thm_PHIP1886_perda_do_bloco
-- name    : PHIP1886.perda_do_bloco
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:01:09.12788+00:00
-- url     : https://prove2.me/theorems/6af04f76-887b-4975-bf2e-ab6b401d08c6
-- title:
--   perda do bloco — PHIP1886
-- statement:
--   Para x,y inteiros, x²+y²−2xy=(y−x)².
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§165.6;166.1;167.8. Declaração PHIP1886.perda_do_bloco; arquivo PHIP1886.lean; SHA-256 52323011b7b43e6c5010035258a3de098246675f7703bb7f8d1627df46bfd66c. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e81ea9b87c905305c280d

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem PHIP1886.perda_do_bloco (x y : Int) : x ^ 2 + y ^ 2 - 2 * (x * y) = (y - x) ^ 2 := by sorry
