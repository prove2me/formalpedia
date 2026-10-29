-- Prove2me | Theorems.Thm_WangGreenTech_Regulation_proposition_3a
-- name    : WangGreenTech.Regulation.proposition_3a
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:51.578978+00:00
-- url     : https://prove2.me/theorems/ffecfafb-f30f-4f39-b9a1-0a02f9a33a6c
-- title:
--   Proposition 3(a) — general development policy
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
--   Assume $b\le b^{(2)}$. Then $2\epsilon\le b^{(1)}<b^{(2)}$; $b^{(1)}$ is strictly increasing in $\epsilon>0$ and in $m_H-m_L\ge0$ with $q,r$ fixed. For every $\lambda\ge0$, $D_\lambda$ is nonempty and bounded below, and the threshold follower profile together with development on $D_\lambda$ is a specified-belief equilibrium.
--
--   If $b\le b^{(1)}$, then for every $\lambda\ge0$,
--   $$D_\lambda=[x_{\rm aggr}^{(1)}(\lambda),\infty).$$
--   If $b>b^{(1)}$, there exist real $\underline\lambda_{\rm aggr}\le\overline\lambda_{\rm aggr}$, independent of $\lambda$, such that for each $\lambda\ge0$ there are real $x\le y\le z$, with $x=x_{\rm aggr}^{(1)}(\lambda)$, satisfying
--   $$D_\lambda=[x,\infty)\quad\text{if }\lambda<\underline\lambda_{\rm aggr}\text{ or }\lambda>\overline\lambda_{\rm aggr},$$
--   $$D_\lambda=[x,y]\cup[z,\infty)\quad\text{if }\underline\lambda_{\rm aggr}\le\lambda\le\overline\lambda_{\rm aggr}.$$
--
--   This expands the entirety of Proposition 1(a) referenced by Proposition 3(a).
--
--   **Formalization Note** Signal thresholds depend on $\lambda$; the two first-mover-advantage bounds do not. Closed intervals include indifferent signals and coalescing roots. Nonemptiness and lower boundedness validate the real infimum. The zero leader coefficient is retained. No separate Proposition 1(a) item is needed.
-- source:
--   Wang, Cho and Scheller-Wolf, Green Technology Development and Adoption: Competition, Regulation, and Uncertainty—A Global Game Approach, Management Science forthcoming artifact, https://doi.org/10.1287/mnsc.2019.3538, body pp. 21–22 (PDF 21–22), Proposition 3(a), expanding Proposition 1(a), body p. 19; Appendix A p. 9 (PDF 42)

import Definitions.Def_WangGreenTech_Regulation_Policies

set_option autoImplicit false

namespace WangGreenTech.Regulation

open Set

theorem proposition_3a (p : Model) (hp : p.Valid) (hb : p.b ≤ followerBound p) :
    2 * p.ε ≤ leaderBound p ∧ leaderBound p < followerBound p ∧
    StrictMonoOn (fun ε => competitionBound ε ((1 - p.q) * (p.mH - p.mL)) p.r) (Ioi 0) ∧
    StrictMonoOn (fun d => competitionBound p.ε ((1 - p.q) * d) p.r) (Ici 0) ∧
    (∀ lam : ℝ, 0 ≤ lam →
      (developmentSet p lam).Nonempty ∧ BddBelow (developmentSet p lam) ∧
      SpecifiedBeliefEquilibrium p (regulation p) lam (thresholdProfile (adoptionCutoff p))
        (endogenousDecision p lam)) ∧
    (p.b ≤ leaderBound p → ∀ lam : ℝ, 0 ≤ lam →
      developmentSet p lam = Ici (developmentCutoff p lam)) ∧
    (leaderBound p < p.b → ∃ lamlo lamhi : ℝ, lamlo ≤ lamhi ∧
      ∀ lam : ℝ, 0 ≤ lam → ∃ x y z : ℝ, x = developmentCutoff p lam ∧ x ≤ y ∧ y ≤ z ∧
        ((lam < lamlo ∨ lamhi < lam) → developmentSet p lam = Ici x) ∧
        (lamlo ≤ lam ∧ lam ≤ lamhi → developmentSet p lam = Icc x y ∪ Ici z)) := by sorry

end WangGreenTech.Regulation
