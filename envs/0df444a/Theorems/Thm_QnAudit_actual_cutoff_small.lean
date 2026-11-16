-- Prove2me | Theorems.Thm_QnAudit_actual_cutoff_small
-- name    : QnAudit.actual_cutoff_small
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:46:48.227448+00:00
-- url     : https://prove2.me/theorems/8b3ef060-4bb4-4f71-94a1-a10f65b30463
-- title:
--   actual cutoff small — QnAudit
-- statement:
--   Vale a desigualdade real exata 1/√((3·10¹²)²−1/4)≤1/4. Ela fornece apenas um limite para o corte numérico declarado.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.actual_cutoff_small; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem QnAudit.actual_cutoff_small :
    1 / Real.sqrt ((3000000000000 : ℝ)^2 - 1/4) ≤ 1/4 := by sorry
