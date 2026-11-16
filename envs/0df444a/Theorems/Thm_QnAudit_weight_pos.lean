-- Prove2me | Theorems.Thm_QnAudit_weight_pos
-- name    : QnAudit.weight_pos
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:51:24.446751+00:00
-- url     : https://prove2.me/theorems/c4172753-f91b-46fb-8f82-32ca82a1ab25
-- title:
--   weight pos — QnAudit
-- statement:
--   Para x real, n natural e t>0, o peso w(x,n,t)=t^(n−1)exp(−xt) é estritamente positivo. A subtração no expoente n−1 é a subtração natural truncada, incluindo n=0.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.weight_pos; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
open MeasureTheory Set
open QnAudit

theorem QnAudit.weight_pos (x : ℝ) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < weight x n t := by sorry
