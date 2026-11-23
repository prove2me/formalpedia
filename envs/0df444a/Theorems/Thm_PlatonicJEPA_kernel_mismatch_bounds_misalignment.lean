-- Prove2me | Theorems.Thm_PlatonicJEPA_kernel_mismatch_bounds_misalignment
-- name    : PlatonicJEPA.kernel_mismatch_bounds_misalignment
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T12:17:40.000801+00:00
-- url     : https://prove2.me/theorems/fcf509a0-5dce-4fd5-b58b-c2cf84a83930
-- title:
--   Theorem 2: kernel mismatch bounds misalignment
-- statement:
--   Let $\pi_1,\pi_2$ share the marginal $p$, let $1\le k$ and $k+1<|Z|$, and let $\Phi_1,\Phi_2$ be spectral embeddings of $\pi_1,\pi_2$ (spectral minimisers: orthonormal top-$k$ eigenvectors, any choice if $K_{\pi_1}$ has ties). Let $\delta=\mu_k-\mu_{k+1}>0$ be the eigengap of $K_{\pi_2}$. Then
--
--   $$\min_{Q\in O(k)}\Big(E_p\|\Phi_1(z)-Q\Phi_2(z)\|^2\Big)^{1/2}\le\frac{2\sqrt2}{\delta}\min\big(\sqrt k\,\|K_{\pi_1}-K_{\pi_2}\|_2,\ \|K_{\pi_1}-K_{\pi_2}\|_F\big).$$
--
--   **Formalization Note** The case $k=|Z|-1$, where $\mu_{k+1}=-\infty$ and the right side is $0$, is not included.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), Section 2.2, Theorem 2, eq. (3), pp. 3-4

import Mathlib
import Definitions.Def_PlatonicJEPA_Basic

open MeasureTheory Filter Topology

namespace PlatonicJEPA

theorem kernel_mismatch_bounds_misalignment {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (π₁ π₂ : Z → Z → ℝ) (h₁π : IsPairLaw p π₁) (h₂π : IsPairLaw p π₂)
    (hk : 1 ≤ k) (hkZ : k + 1 < Fintype.card Z) (hgap : eigs p π₂ (k + 1) < eigs p π₂ k)
    (Φ₁ Φ₂ : Z → Fin k → ℝ) (hΦ₁ : IsSpectralMin p π₁ Φ₁) (hΦ₂ : IsSpectralMin p π₂ Φ₂) :
    ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ,
      Real.sqrt (∑ z, p z * sqNorm (Φ₁ z - rot Q (Φ₂ z))) ≤
        2 * Real.sqrt 2 / (eigs p π₂ k - eigs p π₂ (k + 1)) *
          min (Real.sqrt k * specNorm (kerMat p π₁ - kerMat p π₂))
            (frobNorm (kerMat p π₁ - kerMat p π₂)) := by sorry

end PlatonicJEPA
