-- Prove2me | Theorems.Thm_QnAudit_shell_square_upper
-- name    : QnAudit.shell_square_upper
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:52:05.853411+00:00
-- url     : https://prove2.me/theorems/cd8b3bb2-848c-4c47-8025-734f2f7027c3
-- title:
--   shell square upper — QnAudit
-- statement:
--   Se a=γ²−ε², |ε|<1/2 e a<S+1, então γ²<S+5/4. Todos os parâmetros são reais. O acréscimo correto é 5/4, e não 1.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.shell_square_upper; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem QnAudit.shell_square_upper (a eps gamma S : ℝ)
    (he : |eps| < 1/2) (ha : a = gamma^2-eps^2) (hs : a < S+1) :
    gamma^2 < S+5/4 := by sorry
