-- Prove2me | Theorems.Thm_WangGreenTech_Regulation_lemma_1
-- name    : WangGreenTech.Regulation.lemma_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:53.957463+00:00
-- url     : https://prove2.me/theorems/a41eb39f-761a-4a81-bdab-aa70d4c03365
-- title:
--   Lemma 1 — endogenous-regulation adoption equilibrium
-- statement:
--   Let $p=(\epsilon,b,q,r,f_1,f_L,f_H,m_L,m_H)$ satisfy $\epsilon>0$, $b\ge0$, $0\le q<1$, $r>0$, $f_1,f_L>0$, $f_H\ge f_L$, and $m_L\le m_H\le0$. Signals and the common fundamental are real. Conditional on signal $x$, the specified posterior is uniform on $[x-\epsilon,x+\epsilon]$. Followers form a unit-mass population on $[0,1)$; the leader has zero population mass. Both choose action 1 at indifference.
--
--   For $C\ge0$, define
--   $$B(\epsilon,C,r)=\inf\left(\left\{\frac{2\epsilon+Ct^r}{t}:0<t\le1\right\}\cup\left\{\frac{2\epsilon+C(1-s^r)}{1-s}:0\le s<1\right\}\right).$$
--   Write $b^{(2)}=B(\epsilon,(1-q)(f_H-m_L),r)$ and $b^{(1)}=B(\epsilon,(1-q)(m_H-m_L),r)$.
--
--   The bound satisfies $b^{(2)}>2\epsilon$ and is strictly increasing in $\epsilon>0$ and in the positive difference $f_H-m_L$, with $q,r$ fixed. If $b\le b^{(2)}$, the profile
--   $$\sigma(i,x)=1\quad\Longleftrightarrow\quad x\ge t,\qquad t=\frac b2+f_L-f_H+\frac r{r+1}(1-q)(f_H-m_L)$$
--   is an adoption equilibrium for $R(\alpha)=q+(1-q)\alpha^r$. Its aggregate is $A_t(\theta)=\min\{1,\max\{0,(\theta+\epsilon-t)/(2\epsilon)\}\}$.
--
--   The conclusion constructs a pure symmetric switching equilibrium by checking both follower actions against the actual aggregate and payoffs.
--
--   **Formalization Note** No uniqueness of all equilibria is asserted. Endpoints and adoption at indifference are retained. Integrability and the aggregate formula are conclusions of equilibrium construction. Beliefs are the prescribed kernels (F3).
-- source:
--   Wang, Cho and Scheller-Wolf, Green Technology Development and Adoption: Competition, Regulation, and Uncertainty—A Global Game Approach, Management Science forthcoming artifact, https://doi.org/10.1287/mnsc.2019.3538, body pp. 15–16 (PDF 15–16), Lemma 1; Appendix A pp. 1–3 (PDF 34–36), equations (4)–(7)

import Definitions.Def_WangGreenTech_Regulation_Policies

set_option autoImplicit false

namespace WangGreenTech.Regulation

open Set

theorem lemma_1 (p : Model) (hp : p.Valid) :
    2 * p.ε < followerBound p ∧
    StrictMonoOn (fun ε => competitionBound ε ((1 - p.q) * (p.fH - p.mL)) p.r) (Ioi 0) ∧
    StrictMonoOn (fun d => competitionBound p.ε ((1 - p.q) * d) p.r) (Ioi 0) ∧
    (p.b ≤ followerBound p →
      AdoptionEquilibrium p (regulation p) (thresholdProfile (adoptionCutoff p)) ∧
      (∀ θ, adoptionMass p (thresholdProfile (adoptionCutoff p)) θ =
        thresholdMass p (adoptionCutoff p) θ) ∧
      (∀ i ∈ Ico (0 : ℝ) 1, ∀ x,
        thresholdProfile (adoptionCutoff p) i x = true ↔ adoptionCutoff p ≤ x)) := by sorry

end WangGreenTech.Regulation
