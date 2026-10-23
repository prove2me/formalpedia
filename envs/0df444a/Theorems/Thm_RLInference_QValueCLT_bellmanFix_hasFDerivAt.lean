-- Prove2me | Theorems.Thm_RLInference_QValueCLT_bellmanFix_hasFDerivAt
-- name    : RLInference.QValueCLT.bellmanFix_hasFDerivAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:13:17.966983+00:00
-- url     : https://prove2.me/theorems/4a4131fa-7ffc-4ec3-a608-819d610ce084
-- title:
--   Proof of Theorem 1, p. 36 — φ(r′, P′) is C¹ at (μ_R, P) with ∇φ = −[∂F/∂Q′]⁻¹[∂F/∂r′, ∂F/∂P′]
-- statement:
--   Let $\mathcal S,\mathcal A$ be finite nonempty sets, $0\le\gamma<1$, $r$ a reward vector and $P$ a transition law. Let $Q=\operatorname{Fix}(\gamma,r,P)$ be the Bellman fixed point, and suppose its argmax is unique in every state (Assumption 2): $Q(s,a)<Q(s,a^*(s))$ for all $a\ne a^*(s)$. Let $\phi(r',P')=\operatorname{Fix}(\gamma,r',P')$ be the fixed point as a function of the parameters, on the whole space $\mathbb R^N\times\mathbb R^{Nm_s}$ of reward vectors and real transition arrays. Then:
--   1. on a neighbourhood of $(r,P)$, $\phi(r',P')$ is a fixed point of $\mathcal T_{r',P'}$, i.e. $F(\phi(r',P'),r',P')=0$;
--   2. $\phi$ is continuously differentiable at $(r,P)$;
--   3. its derivative at $(r,P)$ is
--
--   $$\nabla\phi(r,P)[h_r,h_P]=(I-\gamma\tilde P^{\pi^*})^{-1}\Big(h_r+\gamma\big(x\mapsto \textstyle\sum_{k}h_P(k\mid x)\,V^*(k)\big)\Big).$$
--
--   Here $V^*(k)=\max_aQ(k,a)$ and $\tilde P^{\pi^*}((s,a),(s',a'))=P(s'\mid s,a)\mathbb 1(a'=a^*(s'))$. In matrix form, $\nabla\phi=-[\partial F/\partial Q']^{-1}[\partial F/\partial r',\partial F/\partial P']$, with $\partial F/\partial Q'=I-\gamma\tilde P^{\pi^*}$, $\partial F/\partial r'=-I$ and $\partial F/\partial P'=-\gamma\operatorname{blockdiag}((V^*)^T,\dots,(V^*)^T)$.
--
--   This is the gradient used in the delta method: it transfers the CLT (23) for the parameters to $\hat Q_n=\phi(\hat\mu_{R,n},\hat P_n)$.
--
--   **Formalization Note.** The paper's $\phi$ is the implicit function of $F(Q',r',P')=0$ near $(Q,\mu_R,P)$. Here it is the concrete value-iteration limit `bellmanFix`, which coincides with it near $(r,P)$, where $\mathcal T_{r',P'}$ is a sup-norm contraction. Clause 1 records this. The statement is made for an arbitrary reward vector $r$ in place of $\mu_R$; every $r$ is the mean of some reward law. Clause 3 is stated as the existence of a continuous linear map $L$ with `HasFDerivAt` and an explicit formula for $L$.
-- source:
--   Zhu, Dong & Lam, Uncertainty Quantification and Exploration for Reinforcement Learning, arXiv:1910.05471v3, p. 36, App. A.1, second paragraph and the displays for ∇φ, ∂F/∂r′, ∂F/∂P′

import Mathlib
import Definitions.Def_RLInference_QValueCLT_Setting
open MeasureTheory ProbabilityTheory Filter Matrix Topology

namespace RLInference.QValueCLT

theorem bellmanFix_hasFDerivAt {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r : S × A → ℝ) (P : S × A → PMF S) (aStar : S → A)
    (hAstar : ∀ (s : S) (a : A), a ≠ aStar s →
      bellmanFix γ r (Pmat P) (s, a) < bellmanFix γ r (Pmat P) (s, aStar s)) :
    (∀ᶠ θ in 𝓝 (r, Pmat P),
        bellman γ θ.1 θ.2 (bellmanFix γ θ.1 θ.2) = bellmanFix γ θ.1 θ.2) ∧
    ContDiffAt ℝ 1 (fun θ : (S × A → ℝ) × (S × A → S → ℝ) => bellmanFix γ θ.1 θ.2)
      (r, Pmat P) ∧
    ∃ L : ((S × A → ℝ) × (S × A → S → ℝ)) →L[ℝ] (S × A → ℝ),
      HasFDerivAt (fun θ : (S × A → ℝ) × (S × A → S → ℝ) => bellmanFix γ θ.1 θ.2) L
        (r, Pmat P) ∧
      ∀ h : (S × A → ℝ) × (S × A → S → ℝ),
        L h = (1 - γ • PtildeStar (Pmat P) aStar)⁻¹ *ᵥ
          (h.1 + γ • fun x => ∑ k, h.2 x k * Vstar (bellmanFix γ r (Pmat P)) k) := by sorry

end RLInference.QValueCLT
