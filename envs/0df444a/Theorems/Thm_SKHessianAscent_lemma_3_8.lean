-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_3_8
-- name    : SKHessianAscent.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:06:12.36306+00:00
-- url     : https://prove2.me/theorems/c5dcac32-f019-4088-92f2-f8fdb863af0d
-- title:
--   Lemma 3.8 (constants corrected) — boundedness of the dual SDE coefficients $\widehat\Sigma$, $\widehat f^*$ on $\tanh^{-1}(\mathcal S_{\beta,A}(c))$
-- statement:
--   Fix $0<\beta<1$, $c>0$ and a symmetric real $n\times n$ matrix $A$ with $\|A\|_{\mathrm{op}}\le3$; $D(m)=\mathrm{diag}(1/(1-m_i^2))$, $\widehat Q(m)=(\nabla^2_m\mathcal F_{\mathrm{TAP}}(m))^{-1}$, $f$ is the drift (2.4) and $\mathcal S_{\beta,A}(c)$ the safe set. Assume (d3): $\|f(m)-m\|_2\le\varepsilon_{\mathrm{drift}}$ for all $m\in\mathcal S_{\beta,A}(c)$. Put $\kappa=1+\frac{3\beta+3\beta^2}{c}$. Then for every $x\in\mathbb R^n$ with $m=\tanh(x)\in\mathcal S_{\beta,A}(c)$, with $\widehat\Sigma(x)=D(m)\widehat Q(m)$ and $\widehat f^*(x)=\mathbf E_{\mathcal D_n}[\widehat Q(m)^2]D(m)^2m$:
--
--   1. $\|\widehat\Sigma(x)\|_{\mathrm{op}}\le\kappa$;
--   2. $\|\widehat f^*(x)\|_2\le\kappa^2\sqrt n$;
--   3. $\|D(m)\widehat Q(m)(m-f(m))\|_2\le\kappa\,\varepsilon_{\mathrm{drift}}$.
--
--   **Formalization Note** **This is a corrected statement.** The paper prints the constants $c^{-1}$, $c^{-2}$, $c^{-1}$ in place of $\kappa$, $\kappa^2$, $\kappa$ and does not assume $\|A\|_{\mathrm{op}}\le3$. As printed, each of the three bounds fails: Definition 2.2 gives $\|D^{1/2}\widehat QD^{1/2}\|_{\mathrm{op}}\le c^{-1}$, not $\|D\widehat Q\|_{\mathrm{op}}\le c^{-1}$ (for instance $n=3$, $\beta\approx0.656$, $c\approx0.477$, $m\approx(0.981,0.980,0.077)$ gives $c\,\|D\widehat Q\|_{\mathrm{op}}\approx1.61$). The constant $\kappa$ is the one of Lemma 6.1 of the paper, $\|D\widehat Q\|_{\mathrm{op}}\le1+(3\beta+3\beta^2)/c$, valid when $\|A\|_{\mathrm{op}}\le3$, which is the setting of Lemma 3.9 where Lemma 3.8 is used. Lemma 3.9 only needs the coefficients to be bounded, so nothing downstream changes.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3.3, Lemma 3.8, p. 14 (constants corrected; see the note)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_SKWeakPoincare_PathSpace
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Transport
import Definitions.Def_SKHessianAscent_Dynamics

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace SKHessianAscent

theorem lemma_3_8 (β c ε : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hA3 : opNorm A ≤ 3)
    (hd3 : ∀ m ∈ safeSet β A c, l2 (fDrift β A m - m) ≤ ε) :
    ∀ x ∈ dualSafe β A c,
      opNorm (dualSigma β A x) ≤ 1 + (3 * β + 3 * β ^ 2) / c ∧
      l2 (dualPhdDrift β A x) ≤ (1 + (3 * β + 3 * β ^ 2) / c) ^ 2 * Real.sqrt n ∧
      l2 ((dualSigma β A x).mulVec (tanhVec x - fDrift β A (tanhVec x))) ≤
        (1 + (3 * β + 3 * β ^ 2) / c) * ε := by sorry

end SKHessianAscent
