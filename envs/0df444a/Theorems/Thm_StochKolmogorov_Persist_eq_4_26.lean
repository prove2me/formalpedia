-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_eq_4_26
-- name    : StochKolmogorov.Persist.eq_4_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:14.304694+00:00
-- url     : https://prove2.me/theorems/8ab663e7-7381-42fd-80d3-126cf0e672a3
-- title:
--   (4.26), proof of Theorem 4.1, p. 20 — the skeleton chain X(kn*T*) has an invariant π* on ℝⁿ,◦₊ and ‖P(kn*T*, x, ·) − π*‖_TV ≤ C_x r^k
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force. Suppose Assumption 1.2 holds, and let $M>0,\delta_0,H,p,\rho^*,T^*,n^*$ be as in Proposition 4.1 ($T^*$ satisfying the conclusion of Lemma 4.1, $n^*$ satisfying (4.7)).
--
--   The skeleton chain $\{X(kn^*T^*):k\in\mathbb N\}$ has an invariant probability measure $\pi^*$ with $\pi^*(\mathbb R^{n,\circ}_+)=1$, and there is $r\in(0,1)$ such that for every $x\in\mathbb R^{n,\circ}_+$ there is $C_x>0$ with
--   $$\big\|P(kn^*T^*,x,\cdot)-\pi^*(\cdot)\big\|_{TV}\le C_xr^k\qquad\text{for all }k\in\mathbb N.\tag{4.26}$$
--
--   This is geometric ergodicity of the skeleton chain; the paper then passes from the skeleton to continuous time by monotonicity of $t\mapsto\|P(t,x,\cdot)-\pi^*\|_{TV}$.
--
--   **Formalization Note** $\|\mu-\nu\|_{TV}$ is the published `MarkovChainCLT.tvDist`, $\sup_A|\mu(A)-\nu(A)|$ over measurable $A$; the paper does not fix the normalization, and geometric decay is insensitive to a factor $2$. Invariance for the skeleton chain is $\int P(n^*T^*,x,A)\,\pi^*(dx)=\pi^*(A)$ for every measurable $A$. One $r$ serves all $x$; $C_x$ depends on $x$. The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Proof of Theorem 4.1, (4.26), p. 20

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- (4.26), proof of Theorem 4.1 (p. 20): the skeleton chain `(X(k n*T*))_{k ∈ ℕ}` has an invariant
probability measure `π*` on `ℝⁿ,◦₊` and `‖P(k n*T*, x, ·) − π*‖_TV ≤ C_x r^k` with one `r ∈ (0, 1)`
and a constant `C_x > 0` per `x ∈ ℝⁿ,◦₊`. -/
theorem eq_4_26 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n) (hpδ : l1 p = δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (h41 : IsWeightedInvasionMin P C X p ρ)
    (Tstar : ℝ) (hTstar : 0 < Tstar)
    (hT : ∀ T : ℝ, Tstar < T → ∀ x ∈ bdry n, l1 x ≤ M →
      Integrable (Phi C c p) (occMean P X x T) ∧ ∫ y, Phi C c p y ∂(occMean P X x T) ≤ -ρ)
    (nstar : ℕ) (hnstar : Hconst C c γb δ₀ < γb * ((nstar : ℝ) - 1)) :
    ∃ πs : Measure (SDEState n), IsProbabilityMeasure πs ∧ πs (openOrthant n)ᶜ = 0 ∧
      (∀ A : Set (SDEState n), MeasurableSet A →
        ∫⁻ x, trans P X ((nstar : ℝ) * Tstar).toNNReal x A ∂πs = πs A) ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ openOrthant n, ∃ Cx : ℝ, 0 < Cx ∧ ∀ k : ℕ,
        MarkovChainCLT.tvDist (trans P X (k * ((nstar : ℝ) * Tstar).toNNReal) x) πs ≤
          Cx * r ^ k := by sorry

end StochKolmogorov.Persist
