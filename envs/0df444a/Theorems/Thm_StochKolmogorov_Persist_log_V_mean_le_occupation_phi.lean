-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_log_V_mean_le_occupation_phi
-- name    : StochKolmogorov.Persist.log_V_mean_le_occupation_phi
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-01T03:04:23.155334+00:00
-- url     : https://prove2.me/theorems/68b68456-8982-4929-bf9b-226013632e08
-- title:
--   Mean of the logarithmic Lyapunov function along a stochastic Kolmogorov system, (4.8)-(4.9)
-- statement:
--   Let $X$ solve the stochastic Kolmogorov system $dX_i=X_i f_i(X)\,dt+X_i g_i(X)\,dE_i$ from every $x\in\mathbb R^n_+$ under Assumption 1.1 (with $c$, $\gamma_b$), let $\delta_0$ satisfy (3.2), $H$ be the constant of (3.5), and let $p\in\mathbb R^{n,\circ}_+$ with $\|p\|_1\le\delta_0$. With $V(x)=(1+c^\top x)/\prod_i x_i^{p_i}$ as in (3.4) and $\Phi$ as in (4.3), for every $x\in\mathbb R^{n,\circ}_+$ and $T>0$,
--
--   $$\mathbb E_x\ln V(X(T))-\ln V(x)\le \int_0^T\mathbb E_x\,\Phi(X(t))\,dt = T\int\Phi\,d\Pi^x_T.$$
--
--   Role: the expectation of Itô's formula (4.8)-(4.9) for $\ln V(X)$, i.e. $\mathbb E_x G(T)\le\int_0^T\mathbb E_x\Phi(X(t))dt$, used for the first-derivative term in the Taylor expansion of the proof of Proposition 4.1.
--
--   **Formalization Note**: stated as an inequality (the martingale part has mean at most zero); $\Pi^x_T$ is `occMean P X x T`.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, proof of Proposition 4.1, equations (4.8)-(4.9) and (4.14), p. 17-18

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Persist

open EthierKurtz

theorem log_V_mean_le_occupation_phi {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n)
    (hpδ : l1 p ≤ δ₀) :
    ∀ x ∈ openOrthant n, ∀ T : ℝ, 0 < T →
      ∫ ω, Real.log (Vfun c p (X x T.toNNReal ω)) ∂P - Real.log (Vfun c p x) ≤
        T * ∫ y, Phi C c p y ∂(occMean P X x T) := by sorry

end StochKolmogorov.Persist
