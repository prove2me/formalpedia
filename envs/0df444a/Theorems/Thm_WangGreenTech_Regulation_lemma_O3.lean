-- Prove2me | Theorems.Thm_WangGreenTech_Regulation_lemma_O3
-- name    : WangGreenTech.Regulation.lemma_O3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:35.913974+00:00
-- url     : https://prove2.me/theorems/fd95386d-d834-45d7-9b99-c9f2ff6b77f1
-- title:
--   Lemma O3 — shape of the leader’s interim gain
-- statement:
--   Let $p=(\epsilon,b,q,r,f_1,f_L,f_H,m_L,m_H)$ satisfy $\epsilon>0$, $b\ge0$, $0\le q<1$, $r>0$, $f_1,f_L>0$, $f_H\ge f_L$, and $m_L\le m_H\le0$. Signals and the common fundamental are real. Conditional on signal $x$, the specified posterior is uniform on $[x-\epsilon,x+\epsilon]$. Followers form a unit-mass population on $[0,1)$; the leader has zero population mass. Both choose action 1 at indifference.
--
--   For $C\ge0$, define
--   $$B(\epsilon,C,r)=\inf\left(\left\{\frac{2\epsilon+Ct^r}{t}:0<t\le1\right\}\cup\left\{\frac{2\epsilon+C(1-s^r)}{1-s}:0\le s<1\right\}\right).$$
--   Write $b^{(2)}=B(\epsilon,(1-q)(f_H-m_L),r)$ and $b^{(1)}=B(\epsilon,(1-q)(m_H-m_L),r)$.
--
--   The prescribed endogenous adoption threshold is $t=b/2+f_L-f_H+\frac r{r+1}(1-q)(f_H-m_L)$, with aggregate $A_t(\theta)=\min\{1,\max\{0,(\theta+\epsilon-t)/(2\epsilon)\}\}$. Define
--   $$U_D(\lambda,x)=\frac1{2\epsilon}\int_{x-\epsilon}^{x+\epsilon}\left[\lambda-f_1+m_L+\theta-bA_t(\theta)+(q+(1-q)A_t(\theta)^r)(m_H-m_L)\right]d\theta.$$
--   The development set is $D_\lambda=\{x:U_D(\lambda,x)\ge0\}$ and $x_{\rm aggr}^{(1)}(\lambda)=\inf D_\lambda$.
--
--   Assume the standing adoption-existence regime $b\le b^{(2)}$ and fix $\lambda\ge0$. If $b\le b^{(1)}$, $U_D(\lambda,\cdot)$ is nondecreasing on the real line. Otherwise there are real turning points $a<c$ such that
--   $$U_D(\lambda,\cdot)\text{ is strictly increasing on }(-\infty,a],\quad
--   \text{strictly decreasing on }[a,c],\quad
--   \text{strictly increasing on }[c,\infty).$$
--
--   This describes the gain whose zero crossings determine the leader's development policy.
--
--   **Formalization Note** In the first clause, “increases” follows the proof's nonnegative-derivative convention, hence nondecreasing. The second clause requires distinct turning points and strict changes. The function is the operational expected gain, not an arbitrary function with an assumed shape.
-- source:
--   Wang, Cho and Scheller-Wolf, Green Technology Development and Adoption: Competition, Regulation, and Uncertainty—A Global Game Approach, Management Science forthcoming artifact, https://doi.org/10.1287/mnsc.2019.3538, Online Appendix A p. 10 (PDF 43), Lemma O3; proof pp. 11–12 (PDF 44–45)

import Definitions.Def_WangGreenTech_Regulation_Policies

set_option autoImplicit false

namespace WangGreenTech.Regulation

open Set

theorem lemma_O3 (p : Model) (hp : p.Valid) (hb : p.b ≤ followerBound p)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (p.b ≤ leaderBound p → Monotone (endogenousUtility p lam)) ∧
    (leaderBound p < p.b → ∃ a c : ℝ, a < c ∧
      StrictMonoOn (endogenousUtility p lam) (Iic a) ∧
      StrictAntiOn (endogenousUtility p lam) (Icc a c) ∧
      StrictMonoOn (endogenousUtility p lam) (Ici c)) := by sorry

end WangGreenTech.Regulation
