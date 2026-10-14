-- Prove2me | Theorems.Thm_TPG_mixing_contraction
-- name    : TPG.mixing_contraction
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:31:38.304489+00:00
-- url     : https://prove2.me/theorems/b65a0291-7316-4687-bf9d-c0f848bc55b3
-- title:
--   Assumption 1 contracts signed measures of total mass zero: $\|\mu P_q^{a\to b}\|_1\le\gamma^{b-a}\|\mu\|_1$
-- statement:
--   Let the transition matrices $P^t_z$ of the environment satisfy Assumption 1 on the horizon $T$ with a constant $\gamma\ge0$: for every $t<T$, every action $z$ and every pair of probability vectors $f,f'$ on the finite state space $S$, $\|f'P^t_z-fP^t_z\|_{\mathrm{TV}}\le\gamma\,\|f'-f\|_{\mathrm{TV}}$, with $\|\cdot\|_{\mathrm{TV}}=\tfrac12\|\cdot\|_1$.
--
--   **Lemma.** Let $0\le q_s\le1$ for all $s$, let $a\le b\le T$, and let $\mu$ be a real row vector on $S$ with $\sum_x\mu(x)=0$. Then
--
--   $$\bigl\|\mu\,P^a_{q_a}P^{a+1}_{q_{a+1}}\cdots P^{b-1}_{q_{b-1}}\bigr\|_1\le\gamma^{\,b-a}\,\|\mu\|_1,\qquad P^s_\theta=\theta P^s_1+(1-\theta)P^s_0 .$$
--
--   This is the form in which the mixing assumption enters every bias, variance and mixing bound of the source.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is eq. (24), p. 38 (Appendix F.1): by Jordan decomposition the contraction of Assumption 1 extends to signed measures of total mass zero and to multi-step kernels.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem mixing_contraction {S : Type} [Fintype S] [DecidableEq S]
    (E : Env S) (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ T)
    (μ : S → ℝ) (hμ : ∑ x, μ x = 0) :
    ∑ x, |Matrix.vecMul μ (((List.Ico a b).map (fun s => E.PMix (q s) s)).prod) x|
      ≤ γ ^ (b - a) * ∑ x, |μ x| := by sorry
end TPG
