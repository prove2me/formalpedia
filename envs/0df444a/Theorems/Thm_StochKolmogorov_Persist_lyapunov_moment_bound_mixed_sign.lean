-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_lyapunov_moment_bound_mixed_sign
-- name    : StochKolmogorov.Persist.lyapunov_moment_bound_mixed_sign
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T23:46:56.610434+00:00
-- url     : https://prove2.me/theorems/dd178c0f-1219-4f8b-84b3-ba3aec8a3c53
-- title:
--   Lyapunov moment bound (3.6) for exponent vectors of mixed sign
-- statement:
--   Let $X$ solve the stochastic Kolmogorov system $dX_i=X_i f_i(X)\,dt+X_i g_i(X)\,dE_i$ from every $x\in\mathbb R^n_+$ under Assumption 1.1 (with $c$, $\gamma_b$), let $\delta_0$ satisfy (3.2), $H$ be the constant of (3.5), and let $q\in\mathbb R^n$ be an exponent vector of either sign with $|q_i|\le\delta_0$ for all $i$. With $V_q(x)=(1+c^\top x)/\prod_i x_i^{q_i}$ as in (3.4), for every $x\in\mathbb R^{n,\circ}_+$ and $t\ge0$,
--
--   $$\mathbb E_x V_q(X(t))^{\delta_0}\le e^{\delta_0 H t}\,V_q(x)^{\delta_0}.$$
--
--   Role: Lemma 3.1 / (3.6) for the functions $U_i$ of Section 5 (exponents $\hat p_j$ on the support of $\mu$ and $-\check p$ at $i$), and for $V_{-q}$, which bound the exponential moments of $\ln V_q(X(T))-\ln V_q(x)$ in the proof of Proposition 5.1 (copy of the proof of Proposition 4.1).
--
--   **Formalization Note**: the expectation is written as a lower Lebesgue integral of the nonnegative quantity $V_q(X(t))^{\delta_0}$; the generator estimate $\mathcal L V_q^{\delta_0}\le\delta_0 H V_q^{\delta_0}$ holds because $|q_i|\le\delta_0$ is all that (3.5) uses.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, Lemma 3.1, (3.4)-(3.6), p. 7-8, used for the functions U_i in the proof of Proposition 5.1, p. 22

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Persist

open EthierKurtz

theorem lyapunov_moment_bound_mixed_sign {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (q : SDEState n) (hq : ∀ i, |q i| ≤ δ₀)
    (x : SDEState n) (hx : x ∈ openOrthant n) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Vfun c q (X x t ω) ^ δ₀) ∂P ≤
      ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * t) * Vfun c q x ^ δ₀) := by sorry

end StochKolmogorov.Persist
