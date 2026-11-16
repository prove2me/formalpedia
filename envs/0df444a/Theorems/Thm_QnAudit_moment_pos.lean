-- Prove2me | Theorems.Thm_QnAudit_moment_pos
-- name    : QnAudit.moment_pos
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:59:13.585318+00:00
-- url     : https://prove2.me/theorems/ae7cda4f-0c20-4068-bdc2-cba275b99bcf
-- title:
--   moment pos — QnAudit
-- statement:
--   Seja K uma função real estritamente positiva em (0,∞). Para x real e n natural, suponha integrável nesse intervalo t^(n−1)exp(−xt)K(t), com expoente natural truncado. Então o momento dado por essa integral é estritamente positivo.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.moment_pos; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_weight_pos
import Theorems.Thm_QnAudit_positive_integral_Ioi
open MeasureTheory Set
open QnAudit

theorem QnAudit.moment_pos (K : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight x n t * K t) (Ioi 0)) :
    0 < moment K x n := by sorry
