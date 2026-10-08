-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_eq_65
-- name    : SpikedWishart.SoftEdge.eq_65
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:38:24.657907+00:00
-- url     : https://prove2.me/theorems/06577ca0-555d-4cb6-8d47-0513b700ac38
-- title:
--   (65), p. 1656 — Andréief's identity ∫det(f_j(x_k))det(g_j(x_k))Πdµ(x_k) = N!·det(∫f_jg_k dµ)
-- statement:
--   Let $\mu$ be a $\sigma$-finite measure on a measurable space $X$, $N\ge0$, and $f_1,\dots,f_N,g_1,\dots,g_N$ real functions on $X$ such that every product $f_jg_k$ is $\mu$-integrable. Then
--   $$
--   \int_{X^N}\det\big(f_j(x_k)\big)_{j,k=1}^N\,\det\big(g_j(x_k)\big)_{j,k=1}^N\prod_{k=1}^N d\mu(x_k)=N!\,\det\Big(\int_X f_j(x)g_k(x)\,d\mu(x)\Big)_{j,k=1}^N .
--   $$
--
--   This identity (Andréief, 1883) turns the $N$-fold integral of the eigenvalue density into a single $N\times N$ determinant, the step from (64) to (66) in the proof of Proposition 2.1.
--
--   **Formalization Note** The printed (65) omits the factor $N!$ on the left-hand side (it is absorbed into the constant $C'$ of (66)); the true identity is stated here.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1656, §2.1, (65)

import Mathlib
open MeasureTheory

namespace SpikedWishart.SoftEdge

theorem eq_65 {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (N : ℕ)
    (f g : Fin N → α → ℝ) (hfg : ∀ j k, Integrable (fun x => f j x * g k x) μ) :
    ∫ x : Fin N → α, (Matrix.of fun j k => f j (x k)).det * (Matrix.of fun j k => g j (x k)).det
        ∂(Measure.pi fun _ => μ) =
      (N.factorial : ℝ) * (Matrix.of fun j k => ∫ y, f j y * g k y ∂μ).det := by sorry

end SpikedWishart.SoftEdge
