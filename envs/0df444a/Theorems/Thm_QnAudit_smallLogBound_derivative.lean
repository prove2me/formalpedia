-- Prove2me | Theorems.Thm_QnAudit_smallLogBound_derivative
-- name    : QnAudit.smallLogBound_derivative
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:46:19.432242+00:00
-- url     : https://prove2.me/theorems/cdb91e5e-5b1e-4810-b975-f10a7c7c66d4
-- title:
--   smallLogBound derivative — QnAudit
-- statement:
--   Para k,c reais e t>0, defina F(t)=−k/t+(c+1/4)t−log t+log(log(2+1/t²)). Então F′(t)=k/t²+c+1/4−1/t−2/[t(2t²+1)log(2+1/t²)]. O último termo é a contribuição da derivada do logaritmo iterado.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.smallLogBound_derivative; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem QnAudit.smallLogBound_derivative (k c t : ℝ) (ht : 0 < t) :
    HasDerivAt (smallLogBound k c)
      (k / t ^ 2 + c + 1/4 - 1/t -
        2 / (t * (2*t^2+1) * Real.log (2+1/t^2))) t := by sorry
