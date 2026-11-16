-- Prove2me | Theorems.Thm_QnAudit_heat_pos_from_two_regimes
-- name    : QnAudit.heat_pos_from_two_regimes
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:59:18.926573+00:00
-- url     : https://prove2.me/theorems/d8485486-e695-4687-8766-d081c0b2e23c
-- title:
--   heat pos from two regimes — QnAudit
-- statement:
--   Sejam K,H,N,E,r funções reais e t₀ real. Para todo t>0, suponha K=H+N+E, H>0, N≥0 e |E|≤rH. Suponha r(t)<1 tanto no regime t≤t₀ quanto no regime t>t₀. Então K(t)>0 em todo t>0. As cotas dos dois regimes são hipóteses do enunciado.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.heat_pos_from_two_regimes; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_positive_head_controls_signed_tail
open MeasureTheory Set
open QnAudit

theorem QnAudit.heat_pos_from_two_regimes (K H N E r : ℝ → ℝ) (t0 : ℝ)
    (hsplit : ∀ t > 0, K t = H t + N t + E t)
    (hH : ∀ t > 0, 0 < H t) (hN : ∀ t > 0, 0 ≤ N t)
    (hE : ∀ t > 0, |E t| ≤ r t * H t)
    (hsmall : ∀ t > 0, t ≤ t0 → r t < 1)
    (hlarge : ∀ t > 0, t0 < t → r t < 1) :
    ∀ t > 0, 0 < K t := by sorry
