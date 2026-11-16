-- Prove2me | Theorems.Thm_PHIP1886_diferenca_segunda
-- name    : PHIP1886.diferenca_segunda
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:08:45.015089+00:00
-- url     : https://prove2.me/theorems/ec2908be-c042-46bc-b922-e01e71480806
-- title:
--   diferenca segunda — PHIP1886
-- statement:
--   Para h,t,u inteiros com h≥0, defina R(t,u)=max(t−u,0) e H(h,u)=max(h−|u|,0). Então R(t+h,u)−2R(t,u)+R(t−h,u)=H(h,t−u).
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§165.6;166.1;167.8. Declaração PHIP1886.diferenca_segunda; arquivo PHIP1886.lean; SHA-256 52323011b7b43e6c5010035258a3de098246675f7703bb7f8d1627df46bfd66c. Sem reivindicação de novidade. https://app.notion.com/p/41898395ac6e81ea9b87c905305c280d

import Mathlib
import Definitions.Def_RHPF28_PHIP1886_559e0c85eff3
open MeasureTheory Set
open PHIP1886

theorem PHIP1886.diferenca_segunda (h t u : Int) (hh : 0 ≤ h) :
    ramp (t + h) u - 2 * ramp t u + ramp (t - h) u = hat h (t - u) := by sorry
