-- Prove2me | Theorems.Thm_SphereGRF_Holder_legendre_bounds
-- name    : SphereGRF.Holder.legendre_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:28.047163+00:00
-- url     : https://prove2.me/theorems/1120b9c3-2ab4-4b75-b3f8-6024ade87e08
-- title:
--   §4, p. 16 — Legendre polynomial bounds
-- statement:
--   For every degree $\ell\ge0$, $P_\ell(1)=1$ and $P_\ell^{\prime}(1)=\ell(\ell+1)/2$. For $x\in[-1,1]$,
--
--   $$
--   |P_\ell^{\prime}(x)|\le P_\ell^{\prime}(1),\qquad
--   |1-P_\ell(x)|\le |1-x|\frac{\ell(\ell+1)}2,\qquad
--   |1-P_\ell(x)|\le2.
--   $$
--
--   These are the bounds used to control the change of the Legendre polynomial away from $1$ in the covariance kernel estimate.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §4 proof of Lemma 4.2, p. 16, first two displays

import Mathlib
import Definitions.Def_SphereGRF_Holder_Setting

open MeasureTheory ProbabilityTheory Polynomial
noncomputable section

namespace SphereGRF.Holder

theorem legendre_bounds (ℓ : ℕ) :
    (SphereGRF.Spectral.legendreP ℓ).eval 1 = 1 ∧
    (SphereGRF.Spectral.legendreP ℓ).derivative.eval 1 = (ℓ : ℝ) * (ℓ + 1) / 2 ∧
    (∀ x : ℝ, x ∈ Set.Icc (-1) 1 →
      |(SphereGRF.Spectral.legendreP ℓ).derivative.eval x| ≤ (SphereGRF.Spectral.legendreP ℓ).derivative.eval 1) ∧
    (∀ x : ℝ, x ∈ Set.Icc (-1) 1 →
      |1 - (SphereGRF.Spectral.legendreP ℓ).eval x| ≤ |1 - x| * ((ℓ : ℝ) * (ℓ + 1) / 2)) ∧
    (∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |1 - (SphereGRF.Spectral.legendreP ℓ).eval x| ≤ 2) := by sorry

end SphereGRF.Holder
