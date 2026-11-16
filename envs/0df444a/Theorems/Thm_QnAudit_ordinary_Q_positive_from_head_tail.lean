-- Prove2me | Theorems.Thm_QnAudit_ordinary_Q_positive_from_head_tail
-- name    : QnAudit.ordinary_Q_positive_from_head_tail
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:17:14.562273+00:00
-- url     : https://prove2.me/theorems/7207de9d-81cb-4e4c-bebd-1205a1958178
-- title:
--   Lema condicional: ordinary Q positive from head tail — QnAudit
-- statement:
--   Para n≥1,u>0, suponha Q(n,u)=oldQ(K,u,n) e integrabilidade do peso correspondente. Para t>0, suponha K(t)=H(t)+N(t)+E(t), H(t)>0, N(t)≥0 e |E(t)|≤r(t)H(t). Suponha r(t)<1 nos regimes t≤t₀ e t>t₀. Então Q(n,u)>0 para todo n≥1,u>0. Representação, integrabilidade e controle de cauda são hipóteses, não certificados de sua realização em ζ.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.ordinary_Q_positive_from_head_tail; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_heat_pos_from_two_regimes
import Theorems.Thm_QnAudit_ordinary_Q_positive_from_heat_representation
open MeasureTheory Set
open QnAudit

theorem QnAudit.ordinary_Q_positive_from_head_tail (Q : ℕ → ℝ → ℝ) (K H N E r : ℝ → ℝ) (t0 : ℝ)
    (hrep : ∀ n ≥ 1, ∀ u > 0, Q n u = oldQ K u n)
    (hint : ∀ n ≥ 1, ∀ u > 0,
      IntegrableOn (fun t => weight (u ^ 2) n t * K t) (Ioi 0))
    (hsplit : ∀ t > 0, K t = H t + N t + E t)
    (hH : ∀ t > 0, 0 < H t) (hN : ∀ t > 0, 0 ≤ N t)
    (hE : ∀ t > 0, |E t| ≤ r t * H t)
    (hsmall : ∀ t > 0, t ≤ t0 → r t < 1)
    (hlarge : ∀ t > 0, t0 < t → r t < 1) :
    ∀ n ≥ 1, ∀ u > 0, 0 < Q n u := by sorry
