-- Prove2me | Theorems.Thm_WardTakahashi_global_ward_identity
-- name    : WardTakahashi.global_ward_identity
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T21:42:34.66733+00:00
-- url     : https://prove2.me/theorems/91cc4140-1a9d-418e-aa21-52b4cb45b763
-- title:
--   Global Ward identity: $\sum_x\langle\delta_xF\rangle=0$ for a $U(1)$-invariant action
-- statement:
--   Let $S:\mathbb C^N\to\mathbb R$ be continuously differentiable and invariant under global phase rotations, and let $F:\mathbb C^N\to\mathbb C$ be continuously differentiable, with
--   1. $\varphi\mapsto\|\varphi\|\,|F(\varphi)|\,e^{-S(\varphi)}$ integrable, and
--   2. $\varphi\mapsto\|\varphi\|\,\big\|D\big(Fe^{-S}\big)(\varphi)\big\|$ integrable.
--
--   Then
--   $$\sum_{x}\int_{\mathbb C^N}\delta_xF(\varphi)\,e^{-S(\varphi)}\,d\varphi=0 .$$
--
--   Since $\sum_x\delta_xF$ is the variation of $F$ under an infinitesimal global phase rotation, this says the expectation of the symmetry variation of any observable vanishes.
-- source:
--   Wikipedia, "Ward–Takahashi identity" (revision oldid=1374751657), https://en.wikipedia.org/w/index.php?title=Ward%E2%80%93Takahashi_identity&oldid=1374751657 ; section "Derivation in the path integral formulation" (finite-dimensional lattice model)

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

open MeasureTheory Complex

namespace WardTakahashi

theorem global_ward_identity {N : ℕ} (S : FieldConfig N → ℝ) (F : FieldConfig N → ℂ)
    (hS : ContDiff ℝ 1 S) (hF : ContDiff ℝ 1 F) (hinv : IsU1Invariant S)
    (h1 : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖F φ‖ * Real.exp (-S φ)))
    (h2 : Integrable (fun φ : FieldConfig N =>
      ‖φ‖ * ‖fderiv ℝ (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) φ‖)) :
    ∑ x, pathIntegral S (localVar x F) = 0 := by sorry

end WardTakahashi
