-- Prove2me | Theorems.Thm_QnAudit_oldQ_pos
-- name    : QnAudit.oldQ_pos
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:05:30.003743+00:00
-- url     : https://prove2.me/theorems/ac2d6731-a849-4819-b908-1081516226db
-- title:
--   oldQ pos — QnAudit
-- statement:
--   Para u>0 e n natural, suponha K(t)>0 para t>0 e integrabilidade de t^(n−1)exp(−u²t)K(t) em (0,∞). Então oldQ(K,u,n)=2^n u^(2n−1)∫_0^∞ t^(n−1)exp(−u²t)K(t)dt é positivo. Os expoentes naturais usam subtração truncada; não se identifica aqui essa família com ξ ou ζ.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.oldQ_pos; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_moment_pos
open MeasureTheory Set
open QnAudit

theorem QnAudit.oldQ_pos (K : ℝ → ℝ) (u : ℝ) (n : ℕ)
    (hu : 0 < u) (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight (u ^ 2) n t * K t) (Ioi 0)) :
    0 < oldQ K u n := by sorry
