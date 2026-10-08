-- Prove2me | Theorems.Thm_RadGauss_LipschitzGaussian_lemma_13
-- name    : RadGauss.LipschitzGaussian.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:40:25.52121+00:00
-- url     : https://prove2.me/theorems/767c1d31-05ec-43c3-b2f0-6e55b7360802
-- title:
--   Lemma 13 — Slepian's comparison: ‖X_i−X_j‖₂ ≤ ‖Y_i−Y_j‖₂ ⇒ E sup_i X_i ≤ 2 E sup_i Y_i
-- statement:
--   Let $(X_i)_{i\in I}$ and $(Y_i)_{i\in I}$ be centred Gaussian processes indexed by the same finite nonempty set $I$ (each defined on its own probability space). Write $\|X_i - X_j\|_2 = \bigl(\mathbb E (X_i - X_j)^2\bigr)^{1/2}$. If
--
--   $$
--   \|X_i - X_j\|_2 \le \|Y_i - Y_j\|_2 \quad\text{for all } i, j \in I,
--   $$
--
--   then
--
--   $$
--   \mathbb E \max_{i\in I} X_i \le 2\, \mathbb E \max_{i\in I} Y_i .
--   $$
--
--   This is the Gaussian comparison principle (attributed to Slepian, via Pisier) that Bartlett and Mendelson use to compare the Gaussian average of a Lipschitz image of a class with that of the class itself.
--
--   **Formalization Note** The page does not say the processes are centred. Without it the statement is false: the constant processes $X_i \equiv 5$, $Y_i \equiv 0$ are (degenerate) Gaussian processes with all increments $0$, and $5 \le 0$ fails. Slepian's lemma is a statement about centred processes, so mean zero is added for both. The constant $2$ is kept as printed (the sharper Sudakov–Fernique form with constant $1$ is on the platform as `HighDimProb.RandomProcesses.sudakov_fernique_finite_dim`). The index set $\{1,\dots,m\}$ is an arbitrary finite nonempty type, "Gaussian process" is Mathlib's `IsGaussianProcess` (jointly Gaussian finite-dimensional marginals), and $\sup_i$ over a finite set is the maximum.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 471 (PDF p. 9), Lemma 13

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RadGauss.LipschitzGaussian

/-- **Lemma 13** (p. 471), Slepian's comparison as the paper states it, with its constant `2`,
for centred Gaussian processes indexed by a finite nonempty set. The two processes may live on
different probability spaces. -/
theorem lemma_13 {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    {ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → Ω₁ → ℝ) (Y : ι → Ω₂ → ℝ)
    (hX : IsGaussianProcess X P₁) (hY : IsGaussianProcess Y P₂)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P₁ = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P₂ = 0)
    (hinc : ∀ i j, Real.sqrt (∫ ω, (X i ω - X j ω) ^ 2 ∂P₁)
      ≤ Real.sqrt (∫ ω, (Y i ω - Y j ω) ^ 2 ∂P₂)) :
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P₁ ≤
      2 * ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P₂ := by sorry

end RadGauss.LipschitzGaussian
