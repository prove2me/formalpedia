-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_log_lln_squares
-- name    : StochKolmogorov.Classify.log_lln_squares
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T13:23:41.773566+00:00
-- url     : https://prove2.me/theorems/a5257282-d258-4802-b7fb-548e3acafa74
-- title:
--   Strong law of large numbers for the logarithm of a stochastic Kolmogorov system along square times
-- statement:
--   Let $X^x$ solve the stochastic Kolmogorov system (1.1) $dX_i=X_i f_i(X)\,dt+X_i g_i(X)\,dE_i$, $E=\Gamma^\top B$, with $f_i,g_i$ continuous on $\mathbb R^n_+$, started at $x$ in the open orthant, and suppose $X^x$ stays in the open orthant almost surely. If for some $K$, almost surely $\int_0^t g_i(X(u))^2\,du\le Kt$ for all large $t$ and every $i$, then almost surely, for every $i$,
--
--   $$\frac{\ln X_i(m^2)}{m^2}-\frac1{m^2}\int_0^{m^2}\Big(f_i(X(u))-\frac{\sigma_{ii}}2 g_i(X(u))^2\Big)du\longrightarrow 0\qquad(m\to\infty).$$
--
--   Role: the strong law for the martingale part of $\ln X_i$ used in the proof of Lemma 5.4 and Theorem 5.2
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, proof of Lemma 5.4 and of Theorem 5.2 (p. 28): ln X_i(t)/t = ln x_i/t + (1/t) int_0^t h_i + M_i(t)/t with M_i(t)/t -> 0 by the strong law for martingales since <M_i>_t <= K t

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify

open EthierKurtz

theorem log_lln_squares {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (hcont : ∀ i, ContinuousOn (C.f i) (orthant n) ∧ ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (hx : x ∈ openOrthant n)
    (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ openOrthant n) :
    (∃ K : ℝ, ∀ᵐ ω ∂P, ∀ i, ∀ᶠ t : ℝ in atTop,
      ∫ u in (0 : ℝ)..t, C.g i (X x u.toNNReal ω) ^ 2 ≤ K * t) →
    ∀ᵐ ω ∂P, ∀ i, Tendsto (fun m : ℕ =>
      Real.log (X x ((m ^ 2 : ℕ) : ℝ≥0) ω i) / ((m ^ 2 : ℕ) : ℝ)
      - ((m ^ 2 : ℕ) : ℝ)⁻¹ * ∫ u in (0 : ℝ)..((m ^ 2 : ℕ) : ℝ),
          (C.f i (X x u.toNNReal ω) - C.sig i i * C.g i (X x u.toNNReal ω) ^ 2 / 2))
        atTop (𝓝 0) := by sorry

end StochKolmogorov.Classify
