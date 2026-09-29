-- Prove2me | Theorems.Thm_WardTakahashi_local_ward_takahashi
-- name    : WardTakahashi.local_ward_takahashi
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T21:40:59.909881+00:00
-- url     : https://prove2.me/theorems/f360f86f-d40c-4b21-9e9d-0273b57d4d82
-- title:
--   Local Ward–Takahashi identity: $\langle\delta_xF\rangle=\langle F\,\delta_xS\rangle$
-- statement:
--   Let $S:\mathbb C^N\to\mathbb R$ and $F:\mathbb C^N\to\mathbb C$ be continuously (real-)differentiable, let $x$ be a site, and assume
--   1. $\varphi\mapsto\|\varphi\|\,|F(\varphi)|\,e^{-S(\varphi)}$ is integrable, and
--   2. $\varphi\mapsto\|\varphi\|\,\big\|D\big(Fe^{-S}\big)(\varphi)\big\|$ is integrable.
--
--   Then
--   $$\int_{\mathbb C^N}\delta_xF(\varphi)\,e^{-S(\varphi)}\,d\varphi=\int_{\mathbb C^N}F(\varphi)\,\delta_xS(\varphi)\,e^{-S(\varphi)}\,d\varphi,$$
--   i.e. $Z_S[\delta_xF]=Z_S[F\,\delta_xS]$.
--
--   When $S$ is $U(1)$-invariant, $\delta_xS$ is the lattice divergence of the Noether current, and the identity says that the current divergence inserted into a correlation function equals the local variation of the observable: the Euclidean lattice form of the Ward–Takahashi identity.
-- source:
--   Wikipedia, "Ward–Takahashi identity" (revision oldid=1374751657), https://en.wikipedia.org/w/index.php?title=Ward%E2%80%93Takahashi_identity&oldid=1374751657 ; section "Derivation in the path integral formulation" (finite-dimensional lattice model)

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

open MeasureTheory Complex

namespace WardTakahashi

theorem local_ward_takahashi {N : ℕ} (S : FieldConfig N → ℝ) (F : FieldConfig N → ℂ)
    (hS : ContDiff ℝ 1 S) (hF : ContDiff ℝ 1 F) (x : Fin N)
    (h1 : Integrable (fun φ : FieldConfig N => ‖φ‖ * ‖F φ‖ * Real.exp (-S φ)))
    (h2 : Integrable (fun φ : FieldConfig N =>
      ‖φ‖ * ‖fderiv ℝ (fun ψ => F ψ * (Real.exp (-S ψ) : ℂ)) φ‖)) :
    pathIntegral S (localVar x F) = pathIntegral S (fun φ => F φ * ((localVar x S φ : ℝ) : ℂ)) := by sorry

end WardTakahashi
