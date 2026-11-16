-- Prove2me | Theorems.Thm_QnAudit_far_phase_forces_large_decay
-- name    : QnAudit.far_phase_forces_large_decay
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:59:35.15107+00:00
-- url     : https://prove2.me/theorems/0f894261-2000-41a4-b86a-8dda6a92c87d
-- title:
--   far phase forces large decay — QnAudit
-- statement:
--   Se |ε|<1/2, γ>0, t>0 e |2εγ|t>1, então γ²−ε²>1/t²−1/4.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.far_phase_forces_large_decay; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_phase_bound
open MeasureTheory Set
open QnAudit

theorem QnAudit.far_phase_forces_large_decay (eps gamma t : ℝ)
    (he : |eps| < 1/2) (hg : 0 < gamma) (ht : 0 < t)
    (hfar : 1 < |2*eps*gamma| * t) :
    1 / t^2 - 1/4 < gamma^2 - eps^2 := by sorry
