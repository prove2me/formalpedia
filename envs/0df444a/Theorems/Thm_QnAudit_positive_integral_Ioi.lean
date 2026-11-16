-- Prove2me | Theorems.Thm_QnAudit_positive_integral_Ioi
-- name    : QnAudit.positive_integral_Ioi
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:51:26.055175+00:00
-- url     : https://prove2.me/theorems/8f84f9db-225f-437e-9b33-9f8641012765
-- title:
--   positive integral Ioi — QnAudit
-- statement:
--   Se f:(0,∞)→ℝ é estritamente positiva em cada ponto e integrável nesse intervalo em relação à medida de Lebesgue, então sua integral sobre (0,∞) é estritamente positiva.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.positive_integral_Ioi; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem QnAudit.positive_integral_Ioi (f : ℝ → ℝ)
    (hf : ∀ t > 0, 0 < f t)
    (hi : IntegrableOn f (Ioi 0)) :
    0 < ∫ t in Ioi (0 : ℝ), f t := by sorry
