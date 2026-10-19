-- Prove2me | Theorems.Thm_SeqDiagnosis_BeliefRecon_theorem_1
-- name    : SeqDiagnosis.BeliefRecon.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:03.182751+00:00
-- url     : https://prove2.me/theorems/1fdb6bbc-4dfc-4da1-8435-f080207aec42
-- title:
--   Theorem 1, p. 9 — rank and closed-form reconstruction of every reachable posterior
-- statement:
--   Let $f_0,\ldots,f_N$ be the class densities of an exponential-tilting model with natural statistic $h(y)\in\mathbb R^p$ and diagnostic matrix $\mathbb B$. Suppose $\mathbb B=\mathbb R\mathbb P$, where $\mathbb R$ has full column rank $r$ and $\mathbb P$ has full row rank $r$. Let $\theta$ be any prior probability vector. Then $\operatorname{rank}(\mathbb B)=r$. For every nonempty arrival-ordered observation list $y_1,\ldots,y_t$, put $x_t=\mathbb P\sum_{m=1}^t h(y_m)/t$. The posterior obtained by successively applying the Bayesian operator satisfies
--
--   $$\Pi_t(y_1,\ldots,y_t,\theta)=\mathcal T^t(x_t,\theta),$$
--
--   where, for $j=1,\ldots,N$,
--
--   $$\mathcal T_j^t(x,\theta)=\frac{\theta_j\exp\{t(\beta_{j0}+e_j\mathbb R x)\}}{\theta_0+\sum_{i=1}^{N}\theta_i\exp\{t(\beta_{i0}+e_i\mathbb R x)\}},\qquad \mathcal T_0^t(x,\theta)=1-\sum_{j=1}^N\mathcal T_j^t(x,\theta).$$
--
--   The normalizer $\beta_{i0}$ in this transform is computed from row $i$ of $\mathbb R\mathbb P$. For every $t\ge1$, the beliefs reachable after exactly $t$ observations are precisely $\mathcal T^t(\Omega_t,\theta)$, where $\Omega_t$ is the set of attainable diagnostic statistics. If every $\theta_i>0$, then $x\mapsto\mathcal T^t(x,\theta)$ is injective on $\mathbb R^r$.
--
--   The formula recovers all $N+1$ posterior probabilities from the $r$-coordinate statistic, identifying the reduced belief representation used by the paper.
--
--   **Formalization Note** All class densities are measurable; $f_0$ is strictly positive on the admitted observation space and integrates to one; each tilted baseline function is integrable. Observations are a `List` in arrival order, and the observation type carries a reference measure in place of the paper's $dy$. No $\theta_0>0$ condition is imposed for reconstruction. The injectivity clause is a disclosed, full-support interpretation of the paper's phrase 'dimensionality equal to $r$'; a finite reachable set need not have geometric dimension $r$.
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. 9 (PDF 9), Theorem 1; p. 10 (PDF 10), Definition 2

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Model

namespace SeqDiagnosis.BeliefRecon

/-- Theorem 1: rank, closed-form reconstruction, reachable beliefs, and nonredundancy
of the reconstruction coordinates for a prior with full support. -/
theorem theorem_1 {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (hRP : M.Bmat = R * P) (hR : R.rank = r) (hP : P.rank = r)
    (θ : Fin (N + 1) → ℝ) (hθ : θ ∈ stdSimplex ℝ (Fin (N + 1))) :
    M.Bmat.rank = r ∧
    (∀ ys : List Y, ys ≠ [] → belief M.f θ ys = Tcal M R P ys.length (diagStat M P ys) θ) ∧
    (∀ t : ℕ, 1 ≤ t → reachable M.f θ t = beliefManifold M R P θ t) ∧
    ((∀ i, 0 < θ i) → ∀ t : ℕ, 1 ≤ t →
      Function.Injective (fun x : Fin r → ℝ => Tcal M R P t x θ)) := by sorry

end SeqDiagnosis.BeliefRecon
