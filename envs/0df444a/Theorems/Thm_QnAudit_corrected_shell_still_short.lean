-- Prove2me | Theorems.Thm_QnAudit_corrected_shell_still_short
-- name    : QnAudit.corrected_shell_still_short
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:52:14.46072+00:00
-- url     : https://prove2.me/theorems/d587c677-61bd-426f-9abb-1cd3c38761c5
-- title:
--   corrected shell still short — QnAudit
-- statement:
--   Para g,γ reais, se g≥10 e γ²<g²+5/4, então γ−g<1. Não é necessário supor γ≥0 para esta desigualdade unilateral.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.corrected_shell_still_short; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem QnAudit.corrected_shell_still_short (g gamma : ℝ)
    (hg : 10 ≤ g)
    (hs : gamma^2 < g^2+5/4) : gamma-g < 1 := by sorry
