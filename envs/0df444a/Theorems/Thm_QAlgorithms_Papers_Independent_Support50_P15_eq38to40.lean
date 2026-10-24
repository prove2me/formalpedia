-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq38to40
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq38to40
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:45:47.085106+00:00
-- url     : https://prove2.me/theorems/67219e9c-7987-4155-84d3-794426a7f686
-- title:
--   eq38 40
-- statement:
--   Let $\rho:[0,1]\to\mathbb C^{d\times d}$, $d>0$, be a continuous piecewise continuously differentiable path of normalized full-rank states on one fixed support. For any sequence of strict partitions $0=t_0<\cdots<t_k=1$ whose meshes vanish,
--
--   $$\sum_{j=1}^k\operatorname{tr}[(-\log\rho(t_j))(\rho(t_j)-\rho(t_{j-1}))]\longrightarrow\int_0^1\operatorname{tr}[-\dot\rho(t)\log\rho(t)]\,dt=S(\rho(1))-S(\rho(0)).$$
--
--   The integrand is integrable, and its integral equals the integral of the derivative of $\operatorname{tr}[\rho-\rho\log\rho]$. Each summand is the actual heat divided by any positive assigned bath temperature when $H_j=-T_j\log\rho(t_j)$. Any full-rank endpoint pair admits partitions of its linear interpolation making the normalized heat sum arbitrarily close to the entropy change. This covers arbitrary refining partitions and same-support processes after restriction to that support.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 12, eq38-40

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Eqs. (38)--(40), PDF p.12. Arbitrary partitions converge as their mesh vanishes.
All states have full rank on the fixed support; integrability is a conclusion. -/
theorem eq38to40 {d : ℕ} (hd : 0 < d) (a : ℝ → Matrix (Fin d) (Fin d) ℂ)
    (ha : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsDensityMatrix (a t) ∧ fullRank (a t))
    (hc : piecewiseC1 a) :
    let f := fun t => (-deriv a t * cfc Real.log (a t)).trace.re
    (∀ p : EntropyPathPartition, ∀ t : Fin p.k → ℝ, (∀ j, 0 < t j) → partitionHeat a p t = entropyHeatSum a p) ∧
    IntegrableOn f (Set.Icc 0 1) ∧
    (∫ t in (0 : ℝ)..1, f t) =
      ∫ t in (0 : ℝ)..1, deriv (fun u => (a u - a u * cfc Real.log (a u)).trace.re) t ∧
    (∫ t in (0 : ℝ)..1, f t) = difference (a 1) (a 0) ∧
    (∀ p : ℕ → EntropyPathPartition, Tendsto (fun n => mesh (p n)) atTop (nhds 0) →
      Tendsto (fun n => entropyHeatSum a (p n)) atTop (nhds (∫ t in (0 : ℝ)..1, f t))) ∧
    (∀ b c : EntropyState d, fullRank b.val → fullRank c.val → ∀ e > 0,
      ∃ p : EntropyPathPartition, |entropyHeatSum
        (fun t : ℝ => ((1 - t : ℝ) : ℂ) • b.val + (t : ℂ) • c.val) p -
          difference c.val b.val| < e) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
