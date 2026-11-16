-- Prove2me | Theorems.Thm_PHIP1886_engrossamento
-- name    : PHIP1886.engrossamento
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:08:23.830436+00:00
-- url     : https://prove2.me/theorems/2a6a6b30-c440-4d40-b2f4-f25d2f8937b5
-- title:
--   engrossamento — PHIP1886
-- statement:
--   Para h,u inteiros com h≥0, defina H(h,u)=max(h−|u|,0). Então H(2h,u)=H(h,u−h)+2H(h,u)+H(h,u+h). Trata-se da identidade de refinamento do chapéu triangular discreto.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§165.6;166.1;167.8. Declaração PHIP1886.engrossamento; arquivo PHIP1886.lean; SHA-256 52323011b7b43e6c5010035258a3de098246675f7703bb7f8d1627df46bfd66c. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e81ea9b87c905305c280d

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem PHIP1886.engrossamento (h u : Int) (hh : 0 ≤ h) :
    hat (2 * h) u = hat h (u - h) + 2 * hat h u + hat h (u + h) := by sorry
