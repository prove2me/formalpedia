-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_common_basis_gaussian_sum
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.common_basis_gaussian_sum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:51:09.027263+00:00
-- url     : https://prove2.me/theorems/d8d30162-6ac8-4df6-b4cb-ef526d7fbe51
-- title:
--   §9, overlapping supports and common-basis Gaussian sums
-- statement:
--   Let $V=\sum_i\mu_iZ_i\psi_i$ and $W=\sum_i\nu_iZ_i'\psi_i$ be almost surely convergent series in a real separable Banach space, with the two entire normal coefficient families jointly independent. Put $c_i=\sqrt{\mu_i^2+\nu_i^2}$. There are iid standard normals $Z_i''$ with
--   $$\mu_iZ_i+\nu_iZ_i'=c_iZ_i'',\qquad V+W=\sum_ic_iZ_i''\psi_i.$$
--   Under strong uniqueness of admissible deterministic coefficient series, the sum RKHS consists of $\sum_iw_i\psi_i$ with $w_i=0$ whenever $c_i=0$ and $\sum_{c_i>0}w_i^2/c_i^2<\infty$, with this sum as its squared norm. If $\nu_i$ is eventually nonzero and $\mu_i/\nu_i\to0$, then $c_i^2/\nu_i^2\to1$ and the weighted tail norms are equivalent. This does not assert global equality when finitely many zero directions differ.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 19, §9, overlapping supports and common-basis Gaussian sums

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section PathResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- §9, overlapping supports and common-basis Gaussian sums, arXiv:0805.3252v1, PDF p.19.
The ratio conclusion concerns only an eventual nonzero tail. For equal one-dimensional weights the sum has twice the variance and half the squared RKHS norm, so the orthogonal-sum conclusion cannot be asserted without disjoint supports. -/
theorem common_basis_gaussian_sum
{B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [TopologicalSpace.SeparableSpace B]
    (psi : ℕ → B) (mu nu : ℕ → ℝ) (Z Zp : ℕ → Omega → ℝ)
    (hZ : StandardNormals P (Sum.elim Z Zp))
    (V W : Omega → B)
    (hV : @Measurable Omega B _ (borel B) V)
    (hW : @Measurable Omega B _ (borel B) W)
    (hlimV : ∀ᵐ o ∂P, Tendsto
      (fun n => ∑ i ∈ Finset.range n, (mu i * Z i o) • psi i) atTop (𝓝 (V o)))
    (hlimW : ∀ᵐ o ∂P, Tendsto
      (fun n => ∑ i ∈ Finset.range n, (nu i * Zp i o) • psi i) atTop (𝓝 (W o))) :
    let c := fun i => Real.sqrt ((mu i) ^ 2 + (nu i) ^ 2)
    let admissible := fun w : ℕ → ℝ =>
      (∀ i, c i = 0 → w i = 0) ∧
      Summable (fun i => if c i = 0 then 0 else (w i) ^ 2 / (c i) ^ 2)
    (∃ Zpp : ℕ → Omega → ℝ, StandardNormals P Zpp ∧
      (∀ i o, mu i * Z i o + nu i * Zp i o = c i * Zpp i o) ∧
      ∀ᵐ o ∂P, Tendsto
        (fun n => ∑ i ∈ Finset.range n, (c i * Zpp i o) • psi i)
        atTop (𝓝 (V o + W o))) ∧
    ((∀ w : ℕ → ℝ, admissible w →
      Tendsto (fun n => ∑ i ∈ Finset.range n, w i • psi i) atTop (𝓝 0) →
      ∀ i, w i = 0) →
      (∀ w, admissible w → Summable (fun i => w i • psi i)) ∧
      banachRKHS P (fun o => V o + W o) =
        {b | ∃ w, admissible w ∧ b = series psi w} ∧
      ∀ w, admissible w → banachNorm P (fun o => V o + W o) (series psi w) ^ 2 =
        ∑' i, if c i = 0 then 0 else (w i) ^ 2 / (c i) ^ 2) ∧
    ((∀ᶠ i in atTop, nu i ≠ 0) →
      Tendsto (fun i => mu i / nu i) atTop (𝓝 0) →
      Tendsto (fun i => (c i) ^ 2 / (nu i) ^ 2) atTop (𝓝 1) ∧
      ∃ N : ℕ, (∀ i ≥ N, nu i ≠ 0 ∧ (nu i) ^ 2 ≤ (c i) ^ 2 ∧ (c i) ^ 2 ≤ 2 * (nu i) ^ 2) ∧
        ∀ w : ℕ → ℝ,
          Summable (fun i => if N ≤ i then (w i) ^ 2 / (c i) ^ 2 else 0) ↔
          Summable (fun i => if N ≤ i then (w i) ^ 2 / (nu i) ^ 2 else 0)) := by sorry

end PathResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
