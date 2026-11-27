-- Prove2me | Theorems.Thm_TwoStageMatch_Supplement_remark_4
-- name    : TwoStageMatch.Supplement.remark_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:10:57.511887+00:00
-- url     : https://prove2.me/theorems/64cc0cba-2d5d-54bb-8a37-00cd20cb4c52
-- title:
--   Remark 4: some optimum online first-stage matching is a maximum unweighted matching of $G[D_1,S]$
-- statement:
--   Let $G=(D_1\cup D_2,S,E)$ be a weighted two-stage stochastic matching instance (supply weights $w_j\ge0$, availability probabilities $\pi_i\in[0,1]$). There is a first-stage matching $M_1^*$ that is a maximum unweighted (maximum-cardinality) matching of the induced subgraph $G[D_1,S]$ and attains the optimum online benchmark:
--   $$\sum_{j\in S}w_j\mathbb 1\{j\text{ matched in }M_1^*\}+\mathbb E_{\tilde D_2}\big[\text{Max-WeightMatch}^w(\tilde D_2,S\setminus S_1^*)\big]=\mathrm{OPT}_{\mathrm{online}}.$$
--
--   This lets the optimum online policy be written as an optimization over bases of a transversal matroid (Proposition 2), the starting point of the hardness result Theorem 2.
--
--   Differences from the source:
--   - encoding: an optimum online policy picking M₁* in the first stage → a first-stage matching M₁* whose objective (2) equals OPT_online; reason: an online policy is determined by its first-stage matching, the second stage always taking a maximum supply-weighted matching (p.10)
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Remark 4, p.16

import Mathlib
import Definitions.Def_TwoStageMatch_Supplement_Matroid

namespace TwoStageMatch.Supplement

/-- **Remark 4** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.16). There exists an optimum
online policy picking a matching `M₁*` in the first stage, where `M₁*` is a maximum unweighted
matching in the induced subgraph `G[D₁, S]`.

Stated on every instance (any bipartite graph, weights `w ≥ 0`, probabilities `π ∈ [0, 1]`): some
first-stage matching of maximum cardinality attains the maximum `OPT_online` of eq. (2).

**Formalization Note.** An online policy is determined by its first-stage matching `M₁`, the
second stage taking a maximum supply-weighted matching (p.10); its value is `onlineValue I M₁`,
the objective of (2), and `OPT_online` is the published `optOnline`. -/
theorem remark_4 {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁]
    [DecidableEq D₂] [DecidableEq S] (I : Instance D₁ D₂ S) :
    ∃ M, IsMaxCardMatching I.E firstStage Finset.univ M ∧ onlineValue I M = optOnline I := by sorry

end TwoStageMatch.Supplement
