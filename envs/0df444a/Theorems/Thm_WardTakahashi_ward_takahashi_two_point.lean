-- Prove2me | Theorems.Thm_WardTakahashi_ward_takahashi_two_point
-- name    : WardTakahashi.ward_takahashi_two_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T21:44:58.046186+00:00
-- url     : https://prove2.me/theorems/2677ab6a-43cf-4e25-b5eb-d72009a3cde1
-- title:
--   Ward–Takahashi identity for the two-point function of a $U(1)$-invariant lattice field
-- statement:
--   Let $S:\mathbb C^N\to\mathbb R$ be a continuously (real-)differentiable action, invariant under global phase rotations $S(e^{i\theta}\varphi)=S(\varphi)$, and satisfying the moment conditions
--   1. $\varphi\mapsto(1+\|\varphi\|^3)\,e^{-S(\varphi)}$ is integrable, and
--   2. $\varphi\mapsto\|\varphi\|^3\,\|DS(\varphi)\|\,e^{-S(\varphi)}$ is integrable.
--
--   Write $j_x(\varphi)=\delta_xS(\varphi)=DS(\varphi)[g_x\varphi]$ for the lattice divergence of the Noether current at site $x$. Then
--   1. (current conservation) $\sum_x j_x(\varphi)=0$ for every configuration $\varphi$, and
--   2. (Ward–Takahashi identity) for all sites $x,y,z$,
--   $$\int_{\mathbb C^N}j_x(\varphi)\,\varphi_y\overline{\varphi_z}\,e^{-S(\varphi)}\,d\varphi= i\,(\delta_{xy}-\delta_{xz})\int_{\mathbb C^N}\varphi_y\overline{\varphi_z}\,e^{-S(\varphi)}\,d\varphi .$$
--
--   The insertion of the current divergence into the charged two-point function produces only contact terms, one for each charged field, with opposite signs for $\varphi$ and $\overline\varphi$. This is the position-space lattice analogue of the QED identity $k_\mu\mathcal M^{\mu}=-e\sum(\dots)$ of the source, whose right-hand side consists of amplitudes with shifted external momenta.
--
--   **Formalization Note** Euclidean weight $e^{-S}$, unnormalised integrals, and sup norm $\|\varphi\|=\max_y|\varphi_y|$.
-- source:
--   Wikipedia, "Ward–Takahashi identity" (revision oldid=1374751657), https://en.wikipedia.org/w/index.php?title=Ward%E2%80%93Takahashi_identity&oldid=1374751657 ; section "Derivation in the path integral formulation" (finite-dimensional lattice model)

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

open MeasureTheory Complex

namespace WardTakahashi

theorem ward_takahashi_two_point {N : ℕ} (S : FieldConfig N → ℝ)
    (hS : ContDiff ℝ 1 S) (hinv : IsU1Invariant S)
    (hm : Integrable (fun φ : FieldConfig N => (1 + ‖φ‖ ^ 3) * Real.exp (-S φ)))
    (hd : Integrable (fun φ : FieldConfig N => ‖φ‖ ^ 3 * ‖fderiv ℝ S φ‖ * Real.exp (-S φ)))
    (x y z : Fin N) :
    (∀ φ : FieldConfig N, ∑ x', localVar x' S φ = 0) ∧
    pathIntegral S (fun φ => ((localVar x S φ : ℝ) : ℂ) * (φ y * starRingEnd ℂ (φ z)))
      = I * ((if x = y then 1 else 0) - (if x = z then 1 else 0))
          * pathIntegral S (fun φ => φ y * starRingEnd ℂ (φ z)) := by sorry

end WardTakahashi
