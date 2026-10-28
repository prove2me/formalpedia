-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_remark11
-- name    : QAlgorithms.Papers.Independent.Support50.P15.remark11
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:43:29.342607+00:00
-- url     : https://prove2.me/theorems/b841480e-b32f-401d-8344-0bcd8892dc8b
-- title:
--   remark11
-- statement:
--   For each $d\ge2$, fix the single Hamiltonian $H_{\mathrm{opt}}=\operatorname{diag}(-1,0,\ldots,0)$. Every state $\tau_d(s)=\operatorname{diag}(1-s,s/(d-1),\ldots,s/(d-1))$ with $0\le s\le(d-1)/d$ is its thermal state at some extended temperature $T\in[0,+\infty]$. The maximum-variance state $\tau_d(r_d)$ is attained at a strictly positive finite temperature and has heat capacity $N(d)$. For each fixed integer local dimension $l\ge2$,
--
--   $$\lim_{n\to\infty}\frac{N(l^n)}{n^2}=\frac{\log^2l}{4}.$$
--
--   The same fixed Hamiltonian family therefore attains the maximal heat capacity in every particle number; the approximate signs in Eq. (26) specify a leading asymptotic, not equality with $N_d$.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 9, remark11

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Remark 11, PDF p.9: one fixed exponential family and the precise leading asymptotic in (26). -/
theorem remark11 :
    (∀ d : ℕ, 2 ≤ d →
      (∀ s ∈ Set.Icc (0 : ℝ) (massLimit d),
        ∃ t : ℝ≥0∞, gibbsAtTemperature (optimalHamiltonian d) t = family d s) ∧
      (∃ t : ℝ≥0∞, t ≠ 0 ∧ t ≠ ⊤ ∧
        gibbsAtTemperature (optimalHamiltonian d) t = family d (optimalMass d) ∧
        heatCapacity (optimalHamiltonian d) t = maxVariance d)) ∧
    (∀ l : ℕ, 2 ≤ l → Tendsto
      (fun n : ℕ => maxVariance (l ^ n) / ((n : ℝ) ^ 2)) atTop (nhds ((Real.log l) ^ 2 / 4))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
