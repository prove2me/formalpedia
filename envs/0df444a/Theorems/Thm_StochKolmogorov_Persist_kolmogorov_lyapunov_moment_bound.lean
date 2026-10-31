-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_kolmogorov_lyapunov_moment_bound
-- name    : StochKolmogorov.Persist.kolmogorov_lyapunov_moment_bound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T03:51:07.569668+00:00
-- url     : https://prove2.me/theorems/93078155-7ec9-4f96-85f9-2e55d7d23d8c
-- title:
--   The moment bound (3.6) for $V^{\delta_0}$ along the stochastic Kolmogorov system
-- statement:
--   Under Assumption 1.1, for $\delta_0$ as in (3.2), $p\in\mathbb R^{n,\circ}_+$ with $\|p\|\le\delta_0$, $x\in\mathbb R^{n,\circ}_+$, every solution $Y$ from $x$ and every $t\ge0$, with $V(x)=(1+c^\top x)/\prod_ix_i^{p_i}$ and $H$ the constant of (3.5),
--
--   $$\mathbb E\,V^{\delta_0}(Y_t)\le e^{\delta_0Ht}\,V^{\delta_0}(x).\tag{3.6}$$
--
--   Role: clause 4 of Lemma 3.1, the a priori moment estimate (3.6).
--
--   **Formalization Note**: the expectation is a lower Lebesgue integral of the nonnegative quantity $V^{\delta_0}$, so no integrability hypothesis is needed.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, Lemma 3.1 (4), p. 14, with (3.2), (3.5), (3.6), pp. 13-14

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

theorem kolmogorov_lyapunov_moment_bound {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hB : IsStandardBrownian P B) {c p : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) {x : SDEState n} (hx : x ∈ openOrthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Vfun c p (Y t ω) ^ δ₀) ∂P ≤
      ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * t) * Vfun c p x ^ δ₀) := by sorry

end StochKolmogorov.Persist
