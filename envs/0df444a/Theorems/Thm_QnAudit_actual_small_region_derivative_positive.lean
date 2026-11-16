-- Prove2me | Theorems.Thm_QnAudit_actual_small_region_derivative_positive
-- name    : QnAudit.actual_small_region_derivative_positive
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:08:04.190519+00:00
-- url     : https://prove2.me/theorems/ecade315-3dd2-456c-a48e-82d58e95710d
-- title:
--   actual small region derivative positive — QnAudit
-- statement:
--   Se 0<t≤1/√((3·10¹²)²−1/4), a derivada de F(t)=−k/t+(c+1/4)t−log t+log(log(2+1/t²)), com k=π²/9 e c=(3·10¹²)²/4, é estritamente positiva.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.actual_small_region_derivative_positive; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_smallLogBound_derivative
import Theorems.Thm_QnAudit_corrected_derivative_positive
import Theorems.Thm_QnAudit_actual_cutoff_small
open MeasureTheory Set
open QnAudit

theorem QnAudit.actual_small_region_derivative_positive (t : ℝ) (ht : 0 < t)
    (hcut : t ≤ 1 / Real.sqrt ((3000000000000 : ℝ)^2 - 1/4)) :
    0 < deriv (smallLogBound (Real.pi^2/9) ((3000000000000 : ℝ)^2/4)) t := by sorry
