-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_resolvability_existence
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.resolvability_existence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:51:53.164766+00:00
-- url     : https://prove2.me/theorems/39245e3c-452d-49b4-b94f-4302d3069681
-- title:
--   Theorem 2: separate L1 and KL resolvability witnesses
-- statement:
--   Let $W:x\mapsto W_x$ be a classical discrete stochastic channel from $X$ to $Y$, and let $p$ be a probability mass function on $X$. Write $W_p(y)=\sum_xp(x)W_x(y)$. All logarithms are natural, $d(P,Q)=\sum_y|P(y)-Q(y)|$ is the full L1 distance, and $D(P\|Q)$ is extended nonnegative KL divergence, infinite on a support mismatch. Zero-mass terms in the defining KL expression contribute zero.
--
--   For $C>0$, define $\delta=\mathbb P_{p(x)W_x(y)}\{W_x(y)/W_p(y)>C\}$ and $\delta'=\sum_xp(x)\sum_{y:W_x(y)/W_p(y)\le C}W_x(y)^2/W_p(y)$, excluding null joint-support terms before division. Set $\eta(a)=-a\log a$, with $\eta(0)=0$, and
--   $$
--   \phi(t\mid W,p)=\log\sum_y\left(\sum_xp(x)W_x(y)^{1/(1+t)}\right)^{1+t}.
--   $$
--
--   For every positive integer $M$ and every $C>0$, one has $\delta'\le C$ and there is a tuple codebook $\Psi$ of exactly $M$ entries, allowing repetitions, such that
--   $$
--   d(W_\Psi,W_p)\le 2\delta+\sqrt{\delta'/M}.
--   $$
--   If $Y$ is finite, then for every $-1/2\le t<0$ there is a possibly different tuple codebook $\Psi'$ of exactly $M$ entries satisfying both
--   $$
--   D(W_{\Psi'}\|W_p)\le\frac{\log(1+M^t e^{\phi(t\mid W,p)})}{-t},\qquad
--   D(W_{\Psi'}\|W_p)\le\eta(\delta)+\delta\log|Y|+\delta'/M.
--   $$
--   Here $W_\Psi=M^{-1}\sum_{i=1}^M W_{x_i}$. This supplies separate existence guarantees for the two approximation criteria.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 4, Theorem 2, (9)–(11): resolvability existence in full L1 and KL

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF p.4, Theorem 2, (9)–(11). L1 and KL codes may DIFFER;
for fixed t ONE KL witness satisfies BOTH expectation-derived bounds. -/
theorem resolvability_existence {X Y : Type*} (W : X → Y → ℝ≥0∞)
    (hW : IsDiscreteStochastic W) (p : PMF X) (M : ℕ) (hM : 0 < M) (C : ℝ) (hC : 0 < C) :
    deltaPrime W p C ≤ ENNReal.ofReal C ∧
    (∃ b : Book X, b.size = M ∧
      fullL1 (empirical W b) (discreteOutputMixture W p) ≤ ENNReal.ofReal (l1Bound W p C M)) ∧
    (Finite Y → ∀ t : ℝ, -(1 / 2) ≤ t → t < 0 →
      ∃ b : Book X, b.size = M ∧
        (discreteKLDivergence (empirical W b) (discreteOutputMixture W p) : EReal) ≤ klBound W p M t ∧
        discreteKLDivergence (empirical W b) (discreteOutputMixture W p) ≤ ENNReal.ofReal (entropyBound W p M C)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
