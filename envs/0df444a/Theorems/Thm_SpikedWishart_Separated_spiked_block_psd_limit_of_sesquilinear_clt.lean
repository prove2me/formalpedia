-- Prove2me | Theorems.Thm_SpikedWishart_Separated_spiked_block_psd_limit_of_sesquilinear_clt
-- name    : SpikedWishart.Separated.spiked_block_psd_limit_of_sesquilinear_clt
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T02:43:41.664589+00:00
-- url     : https://prove2.me/theorems/49ffd4ff-f284-4246-b893-380ab6aaa53c
-- title:
--   Conditional limit of the spiked block: $\mathbb P\big(x_n-\frac1M D^{1/2}H^{\mathsf T}A_n\bar H D^{1/2}\succeq0\big)\to G_k(t)$ from the sesquilinear CLT and the GUE law
-- statement:
--   Assume the CLT for Gaussian sesquilinear forms `gaussian_sesquilinear_form_clt` and the GUE top-eigenvalue law `gue_top_eigenvalue_cdf`. Let $k\ge1$, $q\ge0$, $M_n\to\infty$, and let $X$ be an $M_n\times(k+q)$ array of i.i.d. standard complex Gaussian entries (law `SpikedWishart.SoftEdge.sampleLaw (M n) (k+q)`), $H=X^{\mathsf T}$. Let $A_n$ be deterministic Hermitian $M_n\times M_n$ matrices with $-C\le A_n\le C$ and $s_0\le\frac1{M_n}\operatorname{tr}A_n^2\le S_1$ ($s_0>0$), let $c\le L_n\le C$ ($c>0$), let $D_n=\operatorname{diag}(L_n,\dots,L_n,d_{n,1},\dots,d_{n,q})$ with $k$ entries $L_n$ and $c\le d_{n,j}\le L_n-c$, and let $x_n\ge x_0>0$ with
--   $$\frac{\sqrt{M_n}\,\big(x_n-L_n\frac1{M_n}\operatorname{Re}\operatorname{tr}A_n\big)}{L_n\sqrt{\frac1{M_n}\operatorname{Re}\operatorname{tr}A_n^2}}\to t .$$
--   Then
--   $$\mathbb P\Big(x_nI-\tfrac1{M_n}D_n^{1/2}HA_nH^*D_n^{1/2}\succeq0\Big)\to G_k(t).$$
--
--   Role: this is the step of the proof after conditioning on the null block: given the null data, $A_n=1+\frac1M Y_2^*(x-S_{22})^{-1}Y_2$ is deterministic, the $k$ spiked coordinates fluctuate like a $k\times k$ GUE at scale $1/\sqrt M$, while the $q$ intermediate spikes are pushed to $+\infty$ after rescaling and drop out.
-- source:
--   Z. D. Bai and J. Yao, Central limit theorems for eigenvalues in a spiked population model, Ann. Inst. H. Poincare Probab. Statist. 44 (2008) 447-474, https://doi.org/10.1214/07-AIHP118, proof of Theorem 3.1 (conditioning on the null block, Schur complement and the sesquilinear-form CLT, Theorem 7.1); J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, Theorem 1.1(b)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder

namespace SpikedWishart.Separated

theorem spiked_block_psd_limit_of_sesquilinear_clt :
  (∀ (r : ℕ) (C s₀ : ℝ), 0 < s₀ → ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    ∀ (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ), (∀ n, (A n).IsHermitian) →
    (∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) →
    (∀ n, s₀ ≤ ((A n * A n).trace).re / M n) →
    ∀ f : Matrix (Fin r) (Fin r) ℂ → ℝ, Continuous f → (∃ B, ∀ X, |f X| ≤ B) →
    Tendsto (fun n => ∫ X, f (((Real.sqrt (M n) / Real.sqrt (((A n * A n).trace).re / M n) : ℝ) : ℂ) •
          ((M n : ℂ)⁻¹ • ((Matrix.of X)ᵀ * A n * ((Matrix.of X)ᵀ)ᴴ) -
            ((M n : ℂ)⁻¹ * (A n).trace) • (1 : Matrix (Fin r) (Fin r) ℂ)))
        ∂(SpikedWishart.SoftEdge.sampleLaw (M n) r))
      atTop (𝓝 (∫ Z, f ((Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ))
        ∂(SpikedWishart.SoftEdge.sampleLaw r r)))) →
  (∀ (k : ℕ), 1 ≤ k → ∀ x : ℝ,
    (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x) →
  ∀ (k q : ℕ), 1 ≤ k → ∀ (C s₀ S₁ c x₀ : ℝ), 0 < s₀ → 0 < c → 0 < x₀ →
    ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    ∀ (A : ∀ n, Matrix (Fin (M n)) (Fin (M n)) ℂ), (∀ n, (A n).IsHermitian) →
    (∀ n, ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) - A n).PosSemidef ∧
      ((C : ℂ) • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ) + A n).PosSemidef) →
    (∀ n, s₀ ≤ ((A n * A n).trace).re / M n) →
    (∀ n, ((A n * A n).trace).re / M n ≤ S₁) →
    ∀ (L : ℕ → ℝ), (∀ n, c ≤ L n ∧ L n ≤ C) →
    ∀ (D : ℕ → Fin (k + q) → ℝ), (∀ n i, D n (Fin.castAdd q i) = L n) →
    (∀ n j, c ≤ D n (Fin.natAdd k j) ∧ D n (Fin.natAdd k j) ≤ L n - c) →
    ∀ (x : ℕ → ℝ), (∀ n, x₀ ≤ x n) → ∀ (t : ℝ),
    Tendsto (fun n => Real.sqrt (M n) * (x n - L n * (((A n).trace).re / M n)) /
        (L n * Real.sqrt (((A n * A n).trace).re / M n))) atTop (𝓝 t) →
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (k + q)).real
      {X | ((x n : ℂ) • (1 : Matrix (Fin (k + q)) (Fin (k + q)) ℂ) -
        (M n : ℂ)⁻¹ • (diagonal (fun j => (Real.sqrt (D n j) : ℂ)) * (Matrix.of X)ᵀ * A n *
          ((Matrix.of X)ᵀ)ᴴ * diagonal (fun j => (Real.sqrt (D n j) : ℂ)))).PosSemidef})
      atTop (𝓝 (G k t)) := by sorry

end SpikedWishart.Separated
