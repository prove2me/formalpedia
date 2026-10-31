-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_iid_approximation_expectations
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.iid_approximation_expectations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:52:31.670233+00:00
-- url     : https://prove2.me/theorems/f2ad9bf1-89d7-43ad-87bb-8852d14462e3
-- title:
--   Lemma 2: expected iid empirical-output approximation
-- statement:
--   Let $W:x\mapsto W_x$ be a classical discrete stochastic channel from $X$ to $Y$, and let $p$ be a probability mass function on $X$. Write $W_p(y)=\sum_xp(x)W_x(y)$. All logarithms are natural, $d(P,Q)=\sum_y|P(y)-Q(y)|$ is the full L1 distance, and $D(P\|Q)$ is extended nonnegative KL divergence, infinite on a support mismatch. Zero-mass terms in the defining KL expression contribute zero.
--
--   For $C>0$, define $\delta=\mathbb P_{p(x)W_x(y)}\{W_x(y)/W_p(y)>C\}$ and $\delta'=\sum_xp(x)\sum_{y:W_x(y)/W_p(y)\le C}W_x(y)^2/W_p(y)$, excluding null joint-support terms before division. Set $\eta(a)=-a\log a$, with $\eta(0)=0$, and
--   $$
--   \phi(t\mid W,p)=\log\sum_y\left(\sum_xp(x)W_x(y)^{1/(1+t)}\right)^{1+t}.
--   $$
--
--   Let $M\ge1$, $C>0$, and let $X_1,\ldots,X_M$ be independent with common law $p$. Define $W_{X^M}=M^{-1}\sum_iW_{X_i}$. Then
--   $$
--   \mathbb E\,d(W_{X^M},W_p)\le2\delta+\sqrt{\delta'/M},
--   $$
--   and, for each $-1/2\le t<0$,
--   $$
--   \mathbb E\,D(W_{X^M}\|W_p)\le\frac{\log(1+M^te^{\phi(t\mid W,p)})}{-t}.
--   $$
--   If $Y$ is finite, also
--   $$
--   \mathbb E\,D(W_{X^M}\|W_p)\le\eta(\delta)+\delta\log|Y|+\delta'/M.
--   $$
--   These are expectations under the actual iid tuple law, including repeated samples. They yield code existence bounds without any finite-input or absolute-continuity hypothesis.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 4, Lemma 2, (12)–(14): expected iid empirical-output approximation

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi, PDF pp.4–5, Lemma 2, (12)–(14): actual iid EXPECTATIONS.
Only (14) needs finite Y; no input finiteness or absolute continuity is assumed. -/
theorem iid_approximation_expectations {X Y : Type*} (W : X → Y → ℝ≥0∞)
    (hW : IsDiscreteStochastic W) (p : PMF X) (M : ℕ) (hM : 0 < M) (C : ℝ) (hC : 0 < C) :
    iidExpectation p M (fun a => fullL1 (tupleOutput W a) (discreteOutputMixture W p)) ≤
      ENNReal.ofReal (l1Bound W p C M) ∧
    (∀ t : ℝ, -(1 / 2) ≤ t → t < 0 →
      (iidExpectation p M (fun a => discreteKLDivergence (tupleOutput W a) (discreteOutputMixture W p)) : EReal) ≤
        klBound W p M t) ∧
    (Finite Y → iidExpectation p M (fun a => discreteKLDivergence (tupleOutput W a) (discreteOutputMixture W p)) ≤
      ENNReal.ofReal (entropyBound W p M C)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
