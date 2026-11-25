-- Prove2me | Theorems.Thm_SpectralBounds_hoffman_key
-- name    : SpectralBounds.hoffman_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:19:14.534929+00:00
-- url     : https://prove2.me/theorems/64f48e2c-e561-5439-9d81-06539fc16cc4
-- title:
--   Spectral Bounds: hoffman key
-- statement:
--   The key inequality behind both Hoffman bounds: apply the Rayleigh lower bound to
--   `z - t • x`, where `x` is an eigenvector and `z` has vanishing quadratic form.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L110-L122
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/SpectralLib/SpectralBounds.lean#L110-L122

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
open Matrix
omit [Nonempty V]

theorem SpectralBounds.hoffman_key (x z : V → ℝ) (θ t : ℝ) (hx : G.adjMatrix ℝ *ᵥ x = θ • x)
    (hz : z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = 0) :
    (⨅ i, hA.eigenvalues i) * (z ⬝ᵥ z - 2 * t * (z ⬝ᵥ x) + t ^ 2 * (x ⬝ᵥ x)) ≤
      -2 * t * θ * (z ⬝ᵥ x) + t ^ 2 * θ * (x ⬝ᵥ x) := by sorry
