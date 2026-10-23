-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_claim_support_Gamma
-- name    : RelaxedEqMDP.Discrete.claim_support_Gamma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:42.341322+00:00
-- url     : https://prove2.me/theorems/a8b25310-99ba-484c-99ba-85a187722fd3
-- title:
--   Proof of Theorem 2.2, pp. 22–23 — the weak limit $\pi^*$ of Gibbs controls lies in $\Gamma(y^\infty)$
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumptions 2.2 and 2.3 hold. Let $(\lambda_n)\subset(0,1]$ decrease to $0$, let $y^n\to y^\infty$ in $\mathbb R^d$, and let $\pi^*\in\Pi$ be such that for every $i\in\mathcal S$ the Gibbs probability measures $\Gamma_{\lambda_n}(y^n,i)(u)\,du$ converge weakly to $\pi^*(i)$. Then
--   $$\pi^*\in\Gamma(y^\infty),$$
--   that is, every $\pi^*(i)$ is carried by the argmax set $E(y^\infty,i)=\arg\max_{u\in U}\{f(0,i,u)+p^u_i\cdot y^\infty\}$.
--
--   This is the concentration step of the vanishing-entropy limit: as $\lambda_n\to0$ the Gibbs measures put asymptotically no mass away from the maximizers.
--
--   **Formalization Note** The proof's subsequences are absorbed into the hypotheses: the statement assumes exactly what holds along them. Weak convergence is tested against bounded continuous functions on $\mathbb R^\ell$. Assumption 2.3 is kept: the proof's step $\mathrm{Leb}(\{u\in U:f(0,i,u)+p^u_i\cdot y^\infty>A-\varepsilon/2\})>0$ needs it (an isolated maximizer would break it).
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, pp. 22–23, proof of Theorem 2.2 (Appendix A.4), claim "π∗ ∈ Γ(y∞)" with (A.10)–(A.11)

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Proof of Theorem 2.2, pp. 22–23, claim `π* ∈ Γ(y^∞)`: under Assumptions 2.2 and 2.3, if
`λ_n ∈ (0,1]`, `λ_n ↓ 0`, `yⁿ → y^∞`, and for each `i` the Gibbs measures `Γ_{λ_n}(yⁿ,i)` converge
weakly to `π*(i)` with `π* ∈ Π`, then each `π*(i)` is carried by `E(y^∞, i)`. -/
theorem claim_support_Gamma {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (p : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℕ → Fin d → A ℓ → ℝ)
    (Theta iota vartheta : ℝ) (hS : Standing U p)
    (h22 : Assumption22 U f p Theta) (h23 : Assumption23 U iota vartheta)
    (lam : ℕ → ℝ) (hlam : IsLamSeq lam) (y : ℕ → Fin d → ℝ) (yinf : Fin d → ℝ)
    (hy : Tendsto y atTop (𝓝 yinf)) (polStar : Control d ℓ) (hpolStar : IsRelaxed U polStar)
    (hweak : ∀ i, WeakTendsto (fun n => gibbsCtrl U f p (lam n) (y n) i) (polStar i)) :
    polStar ∈ GammaSet U f p yinf := by sorry
end RelaxedEqMDP.Discrete
