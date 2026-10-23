-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_eq_A12_A13
-- name    : RelaxedEqMDP.Discrete.eq_A12_A13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:01.893324+00:00
-- url     : https://prove2.me/theorems/be95a070-cb36-43e6-b3be-19fb3f440902
-- title:
--   (A.12)–(A.13), p. 23 — $V^{\Gamma_{\lambda_n}(y^n,\cdot)}_{\lambda_n}\to V^{\pi^*}$
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumptions 2.1, 2.2 and 2.3 hold. Let $(\lambda_n)\subset(0,1]$ decrease to $0$, let $y^n\to y^\infty$, and let $\pi^*\in\Pi$ be such that $\Gamma_{\lambda_n}(y^n,i)\to\pi^*(i)$ weakly for every $i\in\mathcal S$. Then for every $i\in\mathcal S$
--   $$V^{\Gamma_{\lambda_n}(y^n,\cdot)}_{\lambda_n}(i)\longrightarrow V^{\pi^*}(i)\qquad(n\to\infty).$$
--
--   Combined with $y^n=\Psi_{\lambda_n}(y^n)=V^{\Gamma_{\lambda_n}(y^n,\cdot)}_{\lambda_n}$ this gives $y^\infty=V^{\pi^*}\in\Psi(y^\infty)$ (A.13), and Proposition 2.2 concludes.
--
--   **Formalization Note** As in the previous milestone, the subsequences of the proof are absorbed into the hypotheses, and weak convergence is tested against bounded continuous functions. The entropy terms $\lambda_n\delta(1+k)\mathcal H$ are part of $V_{\lambda_n}$ and must vanish in the limit.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 23, proof of Theorem 2.2 (Appendix A.4), (A.12)–(A.13)

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- (A.12)–(A.13), proof of Theorem 2.2, p. 23: under Assumptions 2.1–2.3, if `λ_n ∈ (0,1]`,
`λ_n ↓ 0`, `yⁿ → y^∞`, and `Γ_{λ_n}(yⁿ,i) → π*(i)` weakly for every `i` with `π* ∈ Π`, then
`V_{λ_n}^{Γ_{λ_n}(yⁿ,·)}(i) → V^{π*}(i)` for all `i ∈ S`. -/
theorem eq_A12_A13 {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ)
    (Theta iota vartheta : ℝ) (hS : Standing U p) (h21 : Assumption21 U f δ)
    (h22 : Assumption22 U f p Theta) (h23 : Assumption23 U iota vartheta)
    (lam : ℕ → ℝ) (hlam : IsLamSeq lam) (y : ℕ → Fin d → ℝ) (yinf : Fin d → ℝ)
    (hy : Tendsto y atTop (𝓝 yinf)) (polStar : Control d ℓ) (hpolStar : IsRelaxed U polStar)
    (hweak : ∀ i, WeakTendsto (fun n => gibbsCtrl U f p (lam n) (y n) i) (polStar i)) (i : Fin d) :
    Tendsto (fun n => Vlam U p f δ (lam n) (gibbsCtrl U f p (lam n) (y n)) i) atTop
      (𝓝 (V p f polStar i)) := by sorry
end RelaxedEqMDP.Discrete
