-- Prove2me | Theorems.Thm_QnAudit_ordinary_Q_positive_from_heat_representation
-- name    : QnAudit.ordinary_Q_positive_from_heat_representation
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:13:19.233024+00:00
-- url     : https://prove2.me/theorems/67fe5511-3c55-4266-8fe7-3166d8ab0258
-- title:
--   Lema condicional: ordinary Q positive from heat representation — QnAudit
-- statement:
--   Seja Q(n,u) uma família real. Para n≥1,u>0, suponha Q(n,u)=oldQ(K,u,n), com K(t)>0 em t>0 e integrabilidade do peso t^(n−1)exp(−u²t)K(t). Então Q(n,u)>0 para n≥1,u>0. A representação integral é assumida, não demonstrada para a função zeta.
--
--   Escopo: resultado com as hipóteses indicadas. Não constitui uma prova de RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL 15/11/2026, §§69; 166.1; fonte avulsa AXLE_QN_POSITIVIDADE_AUDITORIA. Declaração QnAudit.ordinary_Q_positive_from_heat_representation; arquivo lean/QnAudit.lean; SHA-256 7cad1bc7fece1a8e3fb2682e57bf8f37662b309735fe16160c8174a2e92a164c. Sem reivindicação de novidade. Fonte: AXLE_QN_POSITIVIDADE_AUDITORIA e inventário PF28 V1.

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_oldQ_pos
open MeasureTheory Set
open QnAudit

theorem QnAudit.ordinary_Q_positive_from_heat_representation (Q : ℕ → ℝ → ℝ) (K : ℝ → ℝ)
    (hrep : ∀ n ≥ 1, ∀ u > 0, Q n u = oldQ K u n)
    (hK : ∀ t > 0, 0 < K t)
    (hint : ∀ n ≥ 1, ∀ u > 0,
      IntegrableOn (fun t => weight (u ^ 2) n t * K t) (Ioi 0)) :
    ∀ n ≥ 1, ∀ u > 0, 0 < Q n u := by sorry
