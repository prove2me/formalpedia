-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_log_V_mean_le_occupation_phi_mixed_sign
-- name    : StochKolmogorov.Persist.log_V_mean_le_occupation_phi_mixed_sign
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T00:03:29.510728+00:00
-- url     : https://prove2.me/theorems/19906910-4906-4487-9ab0-96d549f63efe
-- title:
--   Mean of the logarithmic Lyapunov function for exponent vectors of mixed sign, (4.8)-(4.9)
-- statement:
--   Let $X$ solve the stochastic Kolmogorov system $dX_i=X_i f_i(X)\,dt+X_i g_i(X)\,dE_i$ from every $x\in\mathbb R^n_+$ under Assumption 1.1 (with $c$, $\gamma_b$), let $\delta_0$ satisfy (3.2), $H$ be the constant of (3.5), and let $q\in\mathbb R^n$ be an exponent vector of either sign with $|q_i|\le\delta_0$ for all $i$. With $V_q(x)=(1+c^\top x)/\prod_i x_i^{q_i}$ as in (3.4) and $\Phi_q=c$-bracket$-\sum_i q_i(f_i-\sigma_{ii}g_i^2/2)$ as in (4.3), for every $x\in\mathbb R^{n,\circ}_+$ and $T>0$ such that $\Phi_q(X(t))$ is integrable on $[0,T]\times\Omega$ and $\ln V_q(X(T))$ is integrable,
--
--   $$\mathbb E_x\ln V_q(X(T))-\ln V_q(x)\le \int_0^T\mathbb E_x\,\Phi_q(X(t))\,dt.$$
--
--   Role: the expectation of Itô\'s formula (4.8)-(4.9) for $\ln U_i(X)$ in the proof of Proposition 5.1, i.e. $\mathbb E_x G(T)\le\int_0^T\mathbb E_x\Phi_q(X(t))dt$, which with (5.3) gives $\mathbb E_x G(T)\le-\rho_e T$.
--
--   **Formalization Note**: stated as an inequality (the local-martingale part has mean at most zero); the time integral is written as an integral over $[0,T]\times\Omega$ against Lebesgue measure times $\mathbb P$, matching hypothesis (5.3) of Proposition 5.1.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, proof of Proposition 4.1, (4.8)-(4.9), p. 17-18, applied to U_i in the proof of Proposition 5.1, p. 22

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Persist

open EthierKurtz

theorem log_V_mean_le_occupation_phi_mixed_sign {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (q : SDEState n) (hq : ∀ i, |q i| ≤ δ₀)
    (x : SDEState n) (hx : x ∈ openOrthant n) (T : ℝ) (hT : 0 < T)
    (hPi : Integrable (fun z : ℝ × Ω => Phi C c q (X x z.1.toNNReal z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P))
    (hlogi : Integrable (fun ω => Real.log (Vfun c q (X x T.toNNReal ω))) P) :
    ∫ ω, Real.log (Vfun c q (X x T.toNNReal ω)) ∂P - Real.log (Vfun c q x) ≤
      ∫ z, Phi C c q (X x z.1.toNNReal z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) := by sorry

end StochKolmogorov.Persist
