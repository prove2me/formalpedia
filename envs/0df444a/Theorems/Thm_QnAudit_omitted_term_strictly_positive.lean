-- Prove2me | Theorems.Thm_QnAudit_omitted_term_strictly_positive
-- name    : QnAudit.omitted_term_strictly_positive
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:46:33.001212+00:00
-- url     : https://prove2.me/theorems/03214675-6043-48eb-bbf7-a33cca836fbc
-- title:
--   omitted term strictly positive — QnAudit
-- statement:
--   Para todo t>0, a quantidade 2/[t(2t²+1)log(2+1/t²)] é estritamente positiva.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.omitted_term_strictly_positive; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem QnAudit.omitted_term_strictly_positive (t : ℝ) (ht : 0 < t) :
    0 < 2 / (t * (2*t^2+1) * Real.log (2+1/t^2)) := by sorry
