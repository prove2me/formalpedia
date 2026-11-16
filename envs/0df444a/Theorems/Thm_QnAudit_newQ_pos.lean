-- Prove2me | Theorems.Thm_QnAudit_newQ_pos
-- name    : QnAudit.newQ_pos
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:05:38.365588+00:00
-- url     : https://prove2.me/theorems/853e3b1b-d19b-4126-94bf-53e571dc5592
-- title:
--   newQ pos — QnAudit
-- statement:
--   Para x>0 e n natural, suponha K(t)>0 e integrabilidade de t^(n−1)exp(−xt)K(t) em (0,∞). Então newQ(K,x,n)=x^n/(n−1)! vezes essa integral é positivo. O índice n−1 é natural truncado; a definição abstrata não fornece uma extensão analítica em n=0.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.newQ_pos; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_moment_pos
open MeasureTheory Set
open QnAudit

theorem QnAudit.newQ_pos (K : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight x n t * K t) (Ioi 0)) :
    0 < newQ K x n := by sorry
