-- Prove2me | Theorems.Thm_TimeInconsLQ_Sufficient_theorem_3_2
-- name    : TimeInconsLQ.Sufficient.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:20.785602+00:00
-- url     : https://prove2.me/theorems/bf2add35-740c-47de-907e-a5bb1b627e18
-- title:
--   Theorem 3.2 — a solution of the forward–backward flow (3.6) with Λ satisfying (3.4) is an open-loop equilibrium
-- statement:
--   Assume the standing assumptions of the time-inconsistent LQ model. Let $u^*\in L^2_{\mathcal F}(0,T;\mathbb R^l)$ and suppose that the system
--
--   $$\begin{cases}dX^*_s=[A_sX^*_s+B_s'u^*_s+b_s]\,ds+\sum_{j=1}^d[C^j_sX^*_s+D^j_su^*_s+\sigma^j_s]\,dW^j_s,& s\in[0,T],\quad X^*_0=x_0,\\[2pt] dp(s;t)=-\big[A_s'p(s;t)+\sum_{j=1}^d(C^j_s)'k^j(s;t)+Q_sX^*_s\big]ds+\sum_{j=1}^dk^j(s;t)\,dW^j_s,& s\in[t,T],\\[2pt] p(T;t)=GX^*_T-h\,\mathbb E_t[X^*_T]-\mu_1X^*_t-\mu_2\end{cases}\qquad(3.6)$$
--
--   has a solution $(u^*,X^*,p,k)$ for every $t\in[0,T)$ such that
--
--   $$\Lambda(s;t)=B_sp(s;t)+\sum_{j=1}^d(D^j_s)'k^j(s;t)+R_su^*_s$$
--
--   satisfies condition (3.4): for every $t\in[0,T)$, $\mathbb E_t\int_t^T|\Lambda(s;t)|\,ds<+\infty$ and $\lim_{s\downarrow t}\mathbb E_t[\Lambda(s;t)]=0$ almost surely. Then $u^*$ is an equilibrium control in the sense of Definition 2.1.
--
--   This is the paper's general sufficient condition for open-loop equilibria; the explicit equilibria of §4 (deterministic coefficients) and §5 (mean–variance) are obtained by exhibiting solutions of (3.6) and checking (3.4).
--
--   **Formalization Note.** The conclusion is the model's `IsEquilibrium` (Definition 2.1 with the lower limit along every sequence $\varepsilon_k\downarrow0$, almost surely, for every state of $u^*$ and every state of each perturbed control); it mentions neither $\Lambda$ nor the adjoint flow. Condition (3.4) is the version-robust encoding of the `Adjoint` file. The second adjoint flow (3.2) is not a hypothesis: the paper's proof constructs it.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 7, Theorem 3.2, (3.6), (3.4)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Sufficient_Model
import Definitions.Def_TimeInconsLQ_Sufficient_Adjoint

namespace TimeInconsLQ.Sufficient

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- Theorem 3.2, p. 7: if `u* ∈ L²_𝓕(0, T; ℝˡ)` has a state process `X*` and, for every
`t ∈ [0, T)`, the first adjoint equation (3.1) has a solution `(p(·;t), k(·;t))` on `[t, T]` such
that `Λ(·;t) = B p(·;t) + Σⱼ (Dʲ)ᵀ kʲ(·;t) + R u*` satisfies condition (3.4), then `u*` is an
equilibrium control in the sense of Definition 2.1. -/
theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ} (M : Data Ω n l d)
    (hM : Standing M) (u : ℝ≥0 → Ω → Fin l → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (p : ℝ≥0 → ℝ≥0 → Ω → Fin n → ℝ) (k : ℝ≥0 → Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hu : Admissible M u) (hX : IsState M u X)
    (hp : ∀ t : ℝ≥0, t < M.T → FirstAdjoint M X t (p t) (k t))
    (h34 : Cond34 M (fun t => Lam M u (p t) (k t))) :
    IsEquilibrium M u := by sorry

end TimeInconsLQ.Sufficient
