-- Prove2me | Theorems.Thm_RadGauss_Discrepancy_condSup_lipschitz
-- name    : RadGauss.Discrepancy.condSup_lipschitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:33:11.056247+00:00
-- url     : https://prove2.me/theorems/75970f9f-f7cd-412e-bede-c8c446b91ec5
-- title:
--   Appendix A — the Lipschitz condition |s(n₁) − s(n₂)| ≤ 4|n₂ − n₁|/n
-- statement:
--   Let $\mu$ be a probability measure on $\mathcal X$, $n\ge1$, and $F$ a nonempty class of measurable functions $\mathcal X\to[-1,1]$. For any two integers $N_1, N_2$ that are values of $\sum_{i=1}^n\sigma_i$ for some sign vectors (that is, $N_j \equiv n \pmod 2$ and $|N_j|\le n$),
--
--   $$
--   |s(N_1) - s(N_2)| \le \frac{4\,|N_2 - N_1|}{n}.
--   $$
--
--   This Lipschitz property lets the concentration of $\sum_i\sigma_i$ around $0$ transfer to $s(\sum_i\sigma_i)$ around $s(0)$.
--
--   **Formalization Note** The paper writes the argument for $0\le n_2<n_1\le n$; the bound is used for $N=\sum_i\sigma_i$, which is negative half of the time, so it is stated here for every pair of attainable values (the inequality is symmetric in $N_1,N_2$). Added hypotheses as for the other statements.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 479 (PDF p. 17), Appendix A, display '|s(n_1) − s(n_2)| ≤ 4|n_2 − n_1|/n'

import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- Appendix A, p. 479: the Lipschitz condition `|s(n₁) − s(n₂)| ≤ 4|n₂ − n₁|/n`, stated for
every pair of values attained by `Σ_i σ_i` (the page writes `0 ≤ n₂ < n₁ ≤ n`). -/
theorem condSup_lipschitz {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin n → Bool,
      Measurable fun x : Fin n → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i))
    (N₁ N₂ : ℤ) (hN₁ : ∃ σ : Fin n → Bool, sumSign σ = N₁)
    (hN₂ : ∃ σ : Fin n → Bool, sumSign σ = N₂) :
    |condSup μ n F N₁ - condSup μ n F N₂| ≤ 4 * |(N₂ : ℝ) - N₁| / n := by sorry

end RadGauss.Discrepancy
