-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_eq_4_11
-- name    : StochKolmogorov.Persist.eq_4_11
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-01T00:47:07.736777+00:00
-- url     : https://prove2.me/theorems/79e552d6-b94f-4c78-aac7-d11260f88bec
-- title:
--   Moment bound (4.11) for the reversed Lyapunov function of a stochastic Kolmogorov system
-- statement:
--   Let $X$ solve the stochastic Kolmogorov system $dX_i=X_i f_i(X)\,dt+X_i g_i(X)\,dE_i$ from every $x\in\mathbb R^n_+$ under Assumption 1.1 (with $c$, $\gamma_b$), let $\delta_0$ satisfy (3.2), $H$ be the constant of (3.5), and let $p\in\mathbb R^{n,\circ}_+$ with $\|p\|_1\le\delta_0$. With $\widehat V(x)=(1+c^\top x)\prod_i x_i^{p_i}$, for every $x\in\mathbb R^{n,\circ}_+$ and $t\ge0$,
--
--   $$\mathbb E_x\,\widehat V^{\delta_0}(X(t))\le \widehat V^{\delta_0}(x)\,e^{\delta_0 H t}.$$
--
--   Role: equation (4.11) in the proof of Proposition 4.1; with (3.6) it gives the two-sided exponential moments of $G(T)$ needed to apply Lemma 3.5.
--
--   **Formalization Note**: $\widehat V$ is `Vfun c (-p)` and the expectation is a lower Lebesgue integral of `ENNReal.ofReal`.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, proof of Proposition 4.1, equation (4.11), p. 17

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Persist

open EthierKurtz

theorem eq_4_11 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n)
    (hpδ : l1 p ≤ δ₀) :
    ∀ x ∈ openOrthant n, ∀ t : ℝ≥0,
      ∫⁻ ω, ENNReal.ofReal (Vfun c (-p) (X x t ω) ^ δ₀) ∂P ≤
        ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * t) * Vfun c (-p) x ^ δ₀) := by sorry

end StochKolmogorov.Persist
