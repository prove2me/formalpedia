-- Prove2me | Theorems.Thm_WangGreenTech_Regulation_proposition_4
-- name    : WangGreenTech.Regulation.proposition_4
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:56.99365+00:00
-- url     : https://prove2.me/theorems/740dc327-566e-49ee-9fcf-2db604e35f4d
-- title:
--   Proposition 4 — comparison of calibrated regulation mechanisms
-- statement:
--   Let $p=(\epsilon,b,q,r,f_1,f_L,f_H,m_L,m_H)$ satisfy $\epsilon>0$, $b\ge0$, $0\le q<1$, $r>0$, $f_1,f_L>0$, $f_H\ge f_L$, and $m_L\le m_H\le0$. Signals and the common fundamental are real. Conditional on signal $x$, the specified posterior is uniform on $[x-\epsilon,x+\epsilon]$. Followers form a unit-mass population on $[0,1)$; the leader has zero population mass. Both choose action 1 at indifference.
--
--   The prescribed endogenous adoption threshold is $t=b/2+f_L-f_H+\frac r{r+1}(1-q)(f_H-m_L)$, with aggregate $A_t(\theta)=\min\{1,\max\{0,(\theta+\epsilon-t)/(2\epsilon)\}\}$. Define
--   $$U_D(\lambda,x)=\frac1{2\epsilon}\int_{x-\epsilon}^{x+\epsilon}\left[\lambda-f_1+m_L+\theta-bA_t(\theta)+(q+(1-q)A_t(\theta)^r)(m_H-m_L)\right]d\theta.$$
--   The development set is $D_\lambda=\{x:U_D(\lambda,x)\ge0\}$ and $x_{\rm aggr}^{(1)}(\lambda)=\inf D_\lambda$.
--
--   For a fixed regulation probability $0<\widehat q<1$, put $\widehat t=b/2+f_L-(1-\widehat q)m_L-\widehat q f_H$ and
--   $$U_F(\lambda,x)=\lambda-f_1+m_L+\widehat q(m_H-m_L)+x-\frac b{2\epsilon}\int_{x-\epsilon}^{x+\epsilon}A_{\widehat t}(\theta)\,d\theta.$$
--   Set $\widehat D_\lambda=\{x:U_F(\lambda,x)\ge0\}$ and $\widehat x^{(1)}(\lambda)=\inf\widehat D_\lambda$.
--
--   Suppose $b\le2\epsilon$, and calibrate the two regulation mechanisms by
--   $$\widehat q=q+\frac{1-q}{r+1},$$
--   which makes the period-2 adoption cutoffs equal, $t=\widehat t$. With all these primitives fixed, there exists a real $\widehat\lambda$ such that for every $\lambda\ge0$,
--   $$x_{\rm aggr}^{(1)}(\lambda)\le\widehat x^{(1)}(\lambda)\quad\Longleftrightarrow\quad\lambda\le\widehat\lambda.$$
--
--   This is the paper's comparison of development incentives under equally effective adoption incentives.
--
--   **Formalization Note** This faithful item retains $m_H=m_L$ and a finite real comparison threshold, possibly negative. Finding F1 gives a counterexample on that permitted boundary: the cutoffs coincide for every $\lambda$, so no finite $\widehat\lambda$ works. It remains the mission goal; the corrected item adds a strict payoff gap. The existential comparison threshold precedes the quantifier over $\lambda$. The Lean statement expands the posterior integrals and development-set infima for a self-contained blind audit; a separate, fully proved verification lemma checks that this expansion is definitionally identical to the canonical cutoff comparison.
-- source:
--   Wang, Cho and Scheller-Wolf, Green Technology Development and Adoption: Competition, Regulation, and Uncertainty—A Global Game Approach, Management Science forthcoming artifact, https://doi.org/10.1287/mnsc.2019.3538, body p. 25 (PDF 25), Proposition 4; proof Online Appendix A pp. 13–14 (PDF 46–47)

import Definitions.Def_WangGreenTech_Regulation_Policies

set_option autoImplicit false

namespace WangGreenTech.Regulation

open MeasureTheory Set

theorem proposition_4 (ε b q r f₁ fL fH mL mH qhat : ℝ)
    (hε : 0 < ε) (hb0 : 0 ≤ b) (hq0 : 0 ≤ q) (hq1 : q < 1) (hr : 0 < r)
    (hf₁ : 0 < f₁) (hfL : 0 < fL) (hfH : fL ≤ fH) (hm : mL ≤ mH) (hmH : mH ≤ 0)
    (hqh0 : 0 < qhat) (hqh1 : qhat < 1) (hb : b ≤ 2 * ε)
    (hcal : qhat = q + (1 - q) / (r + 1)) :
  let t : ℝ := b / 2 + fL - fH + r / (r + 1) * (1 - q) * (fH - mL)
  let that : ℝ := b / 2 + fL - (1 - qhat) * mL - qhat * fH
  let A : ℝ → ℝ → ℝ := fun cutoff θ => min 1 (max 0 ((θ + ε - cutoff) / (2 * ε)))
  let E : ℝ → (ℝ → ℝ) → ℝ := fun x h =>
    ∫ θ, h θ ∂((ENNReal.ofReal (2 * ε))⁻¹ • volume.restrict (Icc (x - ε) (x + ε)))
  let UD : ℝ → ℝ → ℝ := fun lam x => E x (fun θ =>
    lam - f₁ + mL + θ - b * A t θ + (q + (1 - q) * (A t θ) ^ r) * (mH - mL))
  let UF : ℝ → ℝ → ℝ := fun lam x => E x (fun θ =>
    lam - f₁ + θ - b * A that θ + qhat * mH + (1 - qhat) * mL)
  ∃ lamhat : ℝ, ∀ lam : ℝ, 0 ≤ lam →
    (sInf {x : ℝ | 0 ≤ UD lam x} ≤ sInf {x : ℝ | 0 ≤ UF lam x} ↔ lam ≤ lamhat) := by sorry

end WangGreenTech.Regulation
