-- Prove2me | Theorems.Thm_WardTakahashi_anomalous_ward_takahashi
-- name    : WardTakahashi.anomalous_ward_takahashi
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T21:43:33.093459+00:00
-- url     : https://prove2.me/theorems/206ef179-692f-479e-a4fd-be00db9ce562
-- title:
--   Anomalous Ward–Takahashi identity: the anomaly is $\operatorname{tr}A$
-- statement:
--   Let $S:\mathbb C^N\to\mathbb R$ and $F:\mathbb C^N\to\mathbb C$ be continuously (real-)differentiable, and let $A:\mathbb C^N\to\mathbb C^N$ be any real-linear map (the generator of the linear field transformation $\varphi\mapsto e^{\varepsilon A}\varphi$). Assume
--   1. $\varphi\mapsto|F(\varphi)|\,e^{-S(\varphi)}$ is integrable,
--   2. $\varphi\mapsto\|\varphi\|\,|F(\varphi)|\,e^{-S(\varphi)}$ is integrable, and
--   3. $\varphi\mapsto\|\varphi\|\,\big\|D\big(Fe^{-S}\big)(\varphi)\big\|$ is integrable.
--
--   Then
--   $$\int_{\mathbb C^N}\Big(DF(\varphi)[A\varphi]-F(\varphi)\,DS(\varphi)[A\varphi]\Big)e^{-S(\varphi)}\,d\varphi=-\operatorname{tr}_{\mathbb R}(A)\int_{\mathbb C^N}F(\varphi)\,e^{-S(\varphi)}\,d\varphi .$$
--
--   The trace $\operatorname{tr}_{\mathbb R}(A)$ (of $A$ as a real-linear map on $\mathbb R^{2N}$) is the infinitesimal Jacobian of the transformation, i.e. the failure of the measure to be invariant; it is the anomaly term. When $\operatorname{tr}A=0$ (e.g. for phase rotations) the ordinary identity is recovered.
-- source:
--   Wikipedia, "Ward–Takahashi identity" (revision oldid=1374751657), https://en.wikipedia.org/w/index.php?title=Ward%E2%80%93Takahashi_identity&oldid=1374751657 ; section "Derivation in the path integral formulation" (finite-dimensional lattice model)

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

open MeasureTheory Complex

namespace WardTakahashi

theorem anomalous_ward_takahashi {N : ℕ} (S : FieldConfig N → ℝ) (F : FieldConfig N → ℂ)
    (A : FieldConfig N →L[ℝ] FieldConfig N) (hS : ContDiff ℝ 1 S) (hF : ContDiff ℝ 1 F)
    (h0 : Integrable (fun φ : FieldConfig N => ‖F φ‖ * Real.exp (-S φ)))
    (h1 : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖F φ‖ * Real.exp (-S φ)))
    (h2 : Integrable (fun φ : FieldConfig N =>
      ‖φ‖ * ‖fderiv ℝ (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) φ‖)) :
    ∫ φ, (fderiv ℝ F φ (A φ) - F φ * (fderiv ℝ S φ (A φ) : ℂ)) * (Real.exp (-S φ) : ℂ)
      = -((LinearMap.trace ℝ (FieldConfig N) (A : FieldConfig N →ₗ[ℝ] FieldConfig N) : ℝ) : ℂ)
          * pathIntegral S F := by sorry

end WardTakahashi
