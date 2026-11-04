-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_log_lln_continuous
-- name    : StochKolmogorov.Classify.log_lln_continuous
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T18:35:16.174259+00:00
-- url     : https://prove2.me/theorems/8e0b6c31-8dd1-4515-9af0-abb9b0e1b515
-- title:
--   Continuous-time strong law for $\ln X_i(t)/t$ of a stochastic Kolmogorov system started in the open orthant
-- statement:
--   Let $X^x$ solve the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$ with $f_i,g_i$ continuous on $\mathbb R^n_+$, started at $x\in\mathbb R^{n,\circ}_+$, and suppose $X^x(t)\in\mathbb R^{n,\circ}_+$ for all $t$ almost surely. If there is a constant $K$ with, almost surely, $\int_0^t g_i^2(X^x(u))\,du\le Kt$ for all $i$ and all large $t$, then almost surely for every $i$
--
--   $$\frac{\ln X_i^x(t)}{t}-\frac1t\int_0^t\Big(f_i(X^x(u))-\frac{\sigma_{ii}g_i^2(X^x(u))}{2}\Big)du\;\longrightarrow\;0\qquad(t\to\infty).$$
--
--   Role: by Itô's formula $\ln X_i(t)=\ln x_i+\int_0^t(f_i-\sigma_{ii}g_i^2/2)\,du+\int_0^t g_i\,dE_i$, and the statement is the strong law of large numbers for the martingale term; in Lemma 5.9 it converts weak convergence of the occupation measures to $\mu$ into the rate $\ln X_i(t)/t\to\lambda_i(\mu)$.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, Ann. Appl. Probab. 28 (2018), https://arxiv.org/abs/1704.06984v1, proof of Lemma 5.9, p. 27, display (5.35) with (5.23) (Itô's formula for ln X_i and the strong law of large numbers for martingales); X. Mao, Stochastic Differential Equations and Applications, 2nd ed., Horwood 2007, https://doi.org/10.1533/9780857099402, Theorem 1.3.4 (strong law of large numbers for local martingales)

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem log_lln_continuous {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hcont : ∀ i, ContinuousOn (C.f i) (orthant n) ∧ ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (hx : x ∈ openOrthant n)
    (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ openOrthant n) :
    (∃ K : ℝ, ∀ᵐ ω ∂P, ∀ i, ∀ᶠ t : ℝ in atTop,
      ∫ u in (0 : ℝ)..t, C.g i (X x u.toNNReal ω) ^ 2 ≤ K * t) →
    ∀ᵐ ω ∂P, ∀ i, Tendsto (fun t : ℝ≥0 =>
      Real.log (X x t ω i) / (t : ℝ)
      - (t : ℝ)⁻¹ * ∫ u in (0 : ℝ)..(t : ℝ),
          (C.f i (X x u.toNNReal ω) - C.sig i i * C.g i (X x u.toNNReal ω) ^ 2 / 2))
        atTop (𝓝 0) := by sorry

end StochKolmogorov.Classify
