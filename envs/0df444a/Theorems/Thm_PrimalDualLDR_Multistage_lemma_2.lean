-- Prove2me | Theorems.Thm_PrimalDualLDR_Multistage_lemma_2
-- name    : PrimalDualLDR.Multistage.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:02.387315+00:00
-- url     : https://prove2.me/theorems/d262c539-58a2-4c04-a65b-4a7acbc7e231
-- title:
--   Lemma 2 — the matrices X_t, S_t of (4.3) exist and are unique
-- statement:
--   Consider the multistage setting of §4 under its standing assumptions ($\mathbb P$ has the nonempty, bounded polyhedral support $\Xi$ of type (2.1) spanning $\mathbb R^k$, $k_1 = 1$) and the linear-conditional-mean assumption $\mathbb E_t(\xi) = M_tP_t\xi$ $\mathbb P$-a.s. Let $M = \mathbb E(\xi\xi^\top)$ and let $P_t$ be the truncation onto the history $\xi^t$. Fix a stage $t$.
--
--   For any given $x_t \in \mathcal L^2_{k^t,n_t}$ and $s_t \in \mathcal L^2_{k^t,m_t}$ there exist unique matrices $X_t \in \mathbb R^{n_t\times k^t}$ and $S_t \in \mathbb R^{m_t\times k^t}$ satisfying
--   $$X_tP_tM = \mathbb E\big(x_t(\xi^t)\,\xi^\top\big) \qquad\text{and}\qquad S_tP_tM = \mathbb E\big(s_t(\xi^t)\,\xi^\top\big). \tag{4.3}$$
--
--   The lemma lets the dual decision-rule problem $\mathcal{MSP}^l$ be rewritten in terms of the finite-dimensional variables $X_t$, $S_t$: because of the truncation operators, it is not obvious that a matrix $X_t$ reproducing the full cross-moment $\mathbb E(x_t(\xi^t)\xi^\top)$ exists.
--
--   **Formalization Note** The two claims are stated as two independent unique-existence statements, one for each rule. $\mathbb E(x_t(\xi^t)\xi^\top)$ is the matrix of Bochner integrals $\int x_{t,i}(\xi^t)\,\xi_j\,d\mathbb P$.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 20, Lemma 2, (4.3)

import Mathlib
import Definitions.Def_PrimalDualLDR_Multistage_Basic
import Definitions.Def_PrimalDualLDR_Multistage_Setting
import Definitions.Def_PrimalDualLDR_Multistage_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.Multistage

/-- Lemma 2 (p. 20): under the standing assumptions of §4 and the linear-conditional-mean assumption
`𝔼_t(ξ) = M_t P_t ξ`, for any given `x_t ∈ 𝓛²_{k^t,n_t}` and `s_t ∈ 𝓛²_{k^t,m_t}` there exist unique
matrices `X_t ∈ ℝ^{n_t × k^t}` and `S_t ∈ ℝ^{m_t × k^t}` satisfying (4.3):
`X_t P_t M = 𝔼(x_t(ξ^t) ξᵀ)` and `S_t P_t M = 𝔼(s_t(ξ^t) ξᵀ)`. -/
theorem lemma_2 (σ : Setting) (hσ : σ.Standing) (hM : σ.LinearCondMean) (t : Fin σ.T) :
    (∀ x : (Fin (σ.kb t) → ℝ) → (Fin (σ.n t) → ℝ), σ.IsL2RuleAt t x →
      ∃! X : Matrix (Fin (σ.n t)) (Fin (σ.kb t)) ℝ, X * σ.Pt t * σ.M = σ.moment t x) ∧
    (∀ s : (Fin (σ.kb t) → ℝ) → (Fin (σ.m t) → ℝ), σ.IsL2RuleAt t s →
      ∃! S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ, S * σ.Pt t * σ.M = σ.moment t s) := by sorry

end PrimalDualLDR.Multistage
