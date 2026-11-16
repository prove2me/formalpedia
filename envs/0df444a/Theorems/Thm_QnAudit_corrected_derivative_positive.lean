-- Prove2me | Theorems.Thm_QnAudit_corrected_derivative_positive
-- name    : QnAudit.corrected_derivative_positive
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:59:28.857476+00:00
-- url     : https://prove2.me/theorems/dfc20ea9-377b-49c4-932b-1107523c5d11
-- title:
--   corrected derivative positive — QnAudit
-- statement:
--   Para k,c,t reais com 0<t≤1/2, c≥0 e k>3t, vale k/t²+c+1/4−1/t−2/[t(2t²+1)log(2+1/t²)]>0.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.corrected_derivative_positive; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_log_factor_ge_one
open MeasureTheory Set
open QnAudit

theorem QnAudit.corrected_derivative_positive (k c t : ℝ)
    (ht : 0 < t) (hsmall : t ≤ 1/2) (hc : 0 ≤ c) (hk : 3*t < k) :
    0 < k / t ^ 2 + c + 1/4 - 1/t -
        2 / (t * (2*t^2+1) * Real.log (2+1/t^2)) := by sorry
