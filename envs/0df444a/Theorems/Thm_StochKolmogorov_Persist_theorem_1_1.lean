-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_theorem_1_1
-- name    : StochKolmogorov.Persist.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:51.198391+00:00
-- url     : https://prove2.me/theorems/1733f857-bfc7-410b-9bec-ac373357d849
-- title:
--   Theorem 1.1, p. 6 — under Assumptions 1.1 and 1.2, X has a unique invariant probability measure π* on ℝⁿ,◦₊ and converges to it exponentially fast in total variation
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force. Suppose moreover that Assumption 1.2 holds: for every $\mu\in\mathrm{Conv}(\mathcal M)$ (finite convex combinations of ergodic invariant probability measures supported on $\partial\mathbb R^n_+$),
--   $$\max_{i=1,\dots,n}\lambda_i(\mu)>0,\qquad \lambda_i(\mu)=\int\Big(f_i(x)-\frac{\sigma_{ii}g_i^2(x)}{2}\Big)\mu(dx).$$
--   Then $X$ is strongly stochastically persistent and converges exponentially fast to its unique invariant probability measure $\pi^*$ on $\mathbb R^{n,\circ}_+$: there is an invariant probability measure $\pi^*$ with $\pi^*(\mathbb R^{n,\circ}_+)=1$, every invariant probability measure $\pi$ with $\pi(\mathbb R^{n,\circ}_+)=1$ equals $\pi^*$, and there is $r\in(0,1)$ such that for every $x\in\mathbb R^{n,\circ}_+$ there is a constant $C_x$ with
--   $$\|P_X(t,x,\cdot)-\pi^*(\cdot)\|_{TV}\le C_x\,r^t\qquad\text{for all }t\ge0 .$$
--   In particular $\lim_{t\to\infty}\|P_X(t,x,\cdot)-\pi^*\|_{TV}=0$ for every $x\in\mathbb R^{n,\circ}_+$, which is (1.3) of Definition 1.1 (strong stochastic persistence).
--
--   The theorem says that if every ergodic population state on the boundary (where some species are absent) is invaded, then all $n$ species coexist: from any initial state with all species present, the distribution of the population converges at a geometric rate to a single stationary distribution that charges only states with all species present.
--
--   **Formalization Note** Uniqueness is among invariant probability measures concentrated on $\mathbb R^{n,\circ}_+$; boundary invariant measures such as $\delta^*$ always exist, so uniqueness among all invariant measures on $\mathbb R^n_+$ would be false. "Exponentially fast" is the form the proof gives ((4.26) and monotonicity in $t$, p. 20): one rate $r$ for all $x$ and a constant $C_x$ per $x$. $\|\cdot\|_{TV}$ is the published `MarkovChainCLT.tvDist` ($\sup_A|\mu(A)-\nu(A)|$, half the variation norm); the page does not fix the factor and exponential convergence does not depend on it. The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Theorem 1.1, p. 6, with Definition 1.1, p. 4, and Theorem 4.1, p. 18

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- Theorem 1.1 (arXiv:1704.06984v1, p. 6): under Assumptions 1.1 and 1.2, `X` has a unique
invariant probability measure `π*` on `ℝⁿ,◦₊` and `‖P_X(t, x, ·) − π*‖_TV ≤ C_x rᵗ` with one
`r ∈ (0, 1)` for all `x ∈ ℝⁿ,◦₊` and a constant `C_x` per `x`. -/
theorem theorem_1_1 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) (h12 : Assumption12 P C X) :
    ∃ πs : Measure (SDEState n), IsInvariant P X πs ∧ πs (openOrthant n)ᶜ = 0 ∧
      (∀ π : Measure (SDEState n), IsInvariant P X π → π (openOrthant n)ᶜ = 0 → π = πs) ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ openOrthant n, ∃ K : ℝ, ∀ t : ℝ≥0,
        MarkovChainCLT.tvDist (trans P X t x) πs ≤ K * r ^ (t : ℝ) := by sorry

end StochKolmogorov.Persist
