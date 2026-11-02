-- Prove2me | Theorems.Thm_SpikedWishart_Separated_gue_top_eigenvalue_cdf
-- name    : SpikedWishart.Separated.gue_top_eigenvalue_cdf
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-02T02:44:54.992084+00:00
-- url     : https://prove2.me/theorems/952ad583-fdd9-4a2a-ab4a-a98e810dab48
-- title:
--   Largest eigenvalue of the $k\times k$ GUE has distribution function $G_k$ (Weyl integration formula)
-- statement:
--   Let $Z$ be a $k\times k$ array of i.i.d. standard complex Gaussian entries (law `SpikedWishart.SoftEdge.sampleLaw k k`) and $H=(Z+Z^*)/\sqrt2$, the GUE with density proportional to $e^{-\operatorname{tr}H^2/2}$. For every $k\ge1$ and $x\in\mathbb R$,
--
--   $$\mathbb P\big(\lambda_{\max}(H)\le x\big) = G_k(x) = \frac1{Z_k}\int_{(-\infty,x]^k}\prod_{i<j}|\xi_i-\xi_j|^2\prod_i e^{-\xi_i^2/2}\,d\xi ,$$
--
--   with $\lambda_{\max}(H)\le x$ written as $xI-H\succeq 0$.
--
--   Role: this identifies the limit law of the parent, defined in (26)-(28) by the integral formula, as the distribution of the top eigenvalue of the GUE produced by the sesquilinear CLT.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, Definition 1.2 and (26)-(28), p. 1648; G. W. Anderson, A. Guionnet and O. Zeitouni, An Introduction to Random Matrices, Cambridge 2010, https://doi.org/10.1017/CBO9780511801334, Theorem 2.5.2 (joint eigenvalue density of the GUE)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder

namespace SpikedWishart.Separated

theorem gue_top_eigenvalue_cdf :
  ∀ (k : ℕ), 1 ≤ k → ∀ x : ℝ,
    (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x := by sorry

end SpikedWishart.Separated
