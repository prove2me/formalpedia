-- Prove2me | Theorems.Thm_QnAudit_phase_bound
-- name    : QnAudit.phase_bound
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:51:42.900043+00:00
-- url     : https://prove2.me/theorems/5078d941-f719-42b1-acb5-3090c1328e91
-- title:
--   phase bound — QnAudit
-- statement:
--   Se ε,γ são reais, |ε|<1/2 e γ>0, então |2εγ|<γ.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.phase_bound; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem QnAudit.phase_bound (eps gamma : ℝ)
    (he : |eps| < 1/2) (hg : 0 < gamma) :
    |2*eps*gamma| < gamma := by sorry
