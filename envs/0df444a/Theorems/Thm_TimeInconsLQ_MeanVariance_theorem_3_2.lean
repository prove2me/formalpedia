-- Prove2me | Theorems.Thm_TimeInconsLQ_MeanVariance_theorem_3_2
-- name    : TimeInconsLQ.MeanVariance.theorem_3_2
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T12:55:17.854194+00:00
-- url     : https://prove2.me/theorems/e6631508-19ed-47b2-a41c-d3d371a3cc52
-- title:
--   Theorem 3.2 — sufficient condition for an open-loop equilibrium (mean–variance module conventions)
-- statement:
--   This is the sufficient condition for an open-loop equilibrium of the time-inconsistent stochastic LQ problem (Hu–Jin–Zhou, Theorem 3.2), stated in the conventions of the mean–variance modules (`Model`, `Adjoint`) so that it can be applied to the mean–variance instance of §5.
--
--   Let $W$ be a standard $d$-dimensional Brownian motion with its natural filtration $(\mathcal F_t)$, horizon $T>0$, and let the data $A,B,C^j,D^j,b,\sigma^j,Q,R,G,h,\mu_1,\mu_2$ satisfy the standing assumptions of §2. Let $u^*\in L^2_{\mathcal F}(0,T;\mathbb R^l)$ and let $X^*$ be a state process of $u^*$, i.e. a solution of
--   $$dX^*_s=[A_sX^*_s+B_s'u^*_s+b_s]\,ds+\sum_{j=1}^d[C^j_sX^*_s+D^j_su^*_s+\sigma^j_s]\,dW^j_s,\qquad X^*_0=x_0 .$$
--   Suppose that for every $t\in[0,T)$ there is a solution $(p(\cdot;t),k(\cdot;t))$ on $[t,T]$ of the first-order adjoint equation
--   $$dp(s;t)=-\Big[A_s'p(s;t)+\sum_{j=1}^d (C^j_s)'k^j(s;t)+Q_sX^*_s\Big]ds+\sum_{j=1}^d k^j(s;t)\,dW^j_s,\qquad p(T;t)=GX^*_T-hE_t[X^*_T]-\mu_1X^*_t-\mu_2,$$
--   such that
--   $$\Lambda(s;t)=B_s\,p(s;t)+\sum_{j=1}^d (D^j_s)'k^j(s;t)+R_su^*_s$$
--   satisfies condition (3.4): $E_t\int_t^T|\Lambda(s;t)|\,ds<\infty$ and $\lim_{s\downarrow t}E_t[\Lambda(s;t)]=0$ almost surely. Then $u^*$ is an equilibrium control in the sense of Definition 2.1.
--
--   Combined with an explicit solution of the adjoint equation and a verification of (3.4), this theorem is how the explicit equilibria of §§4–5 (in particular Theorem 5.4) are established.
--
--   **Formalization Note.** The data, state, cost, spike variation and Definition 2.1 are those of `Definitions.Def_TimeInconsLQ_MeanVariance_Model`; the adjoint equation on $[t,T]$ (`IsFirstAdjointAt`), $\Lambda$ (`Lam`) and condition (3.4) at one $t$ (`Cond34At`) are those of `Definitions.Def_TimeInconsLQ_MeanVariance_Adjoint`. The adjoint pairs are given as families $t\mapsto(p(\cdot;t),k(\cdot;t))$, constrained only for $t<T$. The same theorem in the conventions of the `Sufficient` modules is `TimeInconsLQ.Sufficient.theorem_3_2`; the two versions differ in how (3.4)(b) is encoded (here the version of $E_t[\Lambda(s;t)]$ is only required to be jointly measurable).
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 7, Theorem 3.2 (system (3.6), condition (3.4), Definition 2.1)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_MeanVariance_Model
import Definitions.Def_TimeInconsLQ_MeanVariance_Adjoint

namespace TimeInconsLQ.MeanVariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- Theorem 3.2 (p. 7), in the conventions of the module `Model`/`Adjoint`: if `u ∈ L²_𝓕(0, T; ℝˡ)`
has a state process `X` and, for every `t ∈ [0, T)`, the first adjoint equation (3.1) along `X`
has a solution `(p(·; t), k(·; t))` on `[t, T]` such that
`Λ(·; t) = B p(·; t) + Σⱼ (Dʲ)′ kʲ(·; t) + R u` satisfies condition (3.4), then `u` is an
equilibrium control (Definition 2.1). -/
theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ} (M : Data Ω n l d)
    (hM : M.Standing) (u : ℝ≥0 → Ω → Fin l → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (p : ℝ≥0 → ℝ≥0 → Ω → Fin n → ℝ) (k : ℝ≥0 → Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hu : M.Admissible u) (hX : M.IsState u X)
    (hp : ∀ t : ℝ≥0, t < M.T → M.IsFirstAdjointAt X t (p t) (k t))
    (h34 : ∀ t : ℝ≥0, t < M.T → M.Cond34At t (M.Lam u (p t) (k t))) :
    M.IsEquilibrium u := by sorry

end TimeInconsLQ.MeanVariance
