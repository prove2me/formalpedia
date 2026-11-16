-- Prove2me | Theorems.Thm_QnAudit_previous_derivative_expression_is_not_derivative
-- name    : QnAudit.previous_derivative_expression_is_not_derivative
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:08:19.020493+00:00
-- url     : https://prove2.me/theorems/bd129a6f-997e-4891-bcf9-4ec9017f0b95
-- title:
--   previous derivative expression is not derivative — QnAudit
-- statement:
--   Para k,c reais e t>0, a derivada de F(t)=−k/t+(c+1/4)t−log t+log(log(2+1/t²)) é diferente de k/t²+c+1/4−1/t. A expressão omitida é estritamente positiva, portanto a fórmula antiga não é a derivada correta em nenhum t>0.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.previous_derivative_expression_is_not_derivative; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_smallLogBound_derivative
import Theorems.Thm_QnAudit_omitted_term_strictly_positive
open MeasureTheory Set
open QnAudit

theorem QnAudit.previous_derivative_expression_is_not_derivative (k c t : ℝ) (ht : 0 < t) :
    deriv (smallLogBound k c) t ≠ k / t^2 + c + 1/4 - 1/t := by sorry
