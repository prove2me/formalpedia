-- Prove2me | Theorems.Thm_WangGreenTech_Regulation_lemma_2
-- name    : WangGreenTech.Regulation.lemma_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:54.17999+00:00
-- url     : https://prove2.me/theorems/3e9b3459-145d-4d45-820d-64f36f5a07af
-- title:
--   Lemma 2 — fixed-regulation benchmark equilibrium
-- statement:
--   Let $p=(\epsilon,b,q,r,f_1,f_L,f_H,m_L,m_H)$ satisfy $\epsilon>0$, $b\ge0$, $0\le q<1$, $r>0$, $f_1,f_L>0$, $f_H\ge f_L$, and $m_L\le m_H\le0$. Signals and the common fundamental are real. Conditional on signal $x$, the specified posterior is uniform on $[x-\epsilon,x+\epsilon]$. Followers form a unit-mass population on $[0,1)$; the leader has zero population mass. Both choose action 1 at indifference.
--
--   For a fixed regulation probability $0<\widehat q<1$, put $\widehat t=b/2+f_L-(1-\widehat q)m_L-\widehat q f_H$ and
--   $$U_F(\lambda,x)=\lambda-f_1+m_L+\widehat q(m_H-m_L)+x-\frac b{2\epsilon}\int_{x-\epsilon}^{x+\epsilon}A_{\widehat t}(\theta)\,d\theta.$$
--   Set $\widehat D_\lambda=\{x:U_F(\lambda,x)\ge0\}$ and $\widehat x^{(1)}(\lambda)=\inf\widehat D_\lambda$.
--
--   Suppose $b\le2\epsilon$. Followers' threshold profile at $\widehat t$ is an adoption equilibrium, with
--   $$\sigma(i,x)=1\quad\Longleftrightarrow\quad x\ge\widehat t,$$
--   and conditional aggregate $A_{\widehat t}(\theta)$. For every $\lambda\ge0$, $\widehat D_\lambda$ is nonempty and bounded below and
--   $$\widehat D_\lambda=[\widehat x^{(1)}(\lambda),\infty).$$
--   Together with this follower profile, the leader's decision to develop precisely on $\widehat D_\lambda$ forms a specified-belief equilibrium.
--
--   This supplies both the adoption threshold and the development cutoff for the benchmark.
--
--   **Formalization Note** $\widehat q$ is independent of aggregate adoption; it is not identified with $q$. No calibration is imposed in Lemma 2. The unused endogenous parameters $q,r$ remain in the shared model record. Their admissible values do not affect the benchmark payoffs.
-- source:
--   Wang, Cho and Scheller-Wolf, Green Technology Development and Adoption: Competition, Regulation, and Uncertainty—A Global Game Approach, Management Science forthcoming artifact, https://doi.org/10.1287/mnsc.2019.3538, body p. 24 (PDF 24), Lemma 2(a)–(b); Appendix A p. 13 (PDF 46), equation (19)

import Definitions.Def_WangGreenTech_Regulation_Policies

set_option autoImplicit false

namespace WangGreenTech.Regulation

open Set

theorem lemma_2 (p : Model) (hp : p.Valid) (qhat : ℝ)
    (hq0 : 0 < qhat) (hq1 : qhat < 1) (hb : p.b ≤ 2 * p.ε) :
    AdoptionEquilibrium p (fun _ => qhat) (thresholdProfile (fixedAdoptionCutoff p qhat)) ∧
    (∀ θ, adoptionMass p (thresholdProfile (fixedAdoptionCutoff p qhat)) θ =
      thresholdMass p (fixedAdoptionCutoff p qhat) θ) ∧
    (∀ i ∈ Ico (0 : ℝ) 1, ∀ x,
      thresholdProfile (fixedAdoptionCutoff p qhat) i x = true ↔ fixedAdoptionCutoff p qhat ≤ x) ∧
    (∀ lam : ℝ, 0 ≤ lam →
      (fixedDevelopmentSet p qhat lam).Nonempty ∧ BddBelow (fixedDevelopmentSet p qhat lam) ∧
      fixedDevelopmentSet p qhat lam = Ici (fixedDevelopmentCutoff p qhat lam) ∧
      SpecifiedBeliefEquilibrium p (fun _ => qhat) lam
        (thresholdProfile (fixedAdoptionCutoff p qhat)) (fixedDecision p qhat lam)) := by sorry

end WangGreenTech.Regulation
