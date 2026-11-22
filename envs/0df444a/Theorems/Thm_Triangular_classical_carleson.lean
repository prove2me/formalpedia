-- Prove2me | Theorems.Thm_Triangular_classical_carleson
-- name    : Triangular.classical_carleson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:29:23.375911+00:00
-- url     : https://prove2.me/theorems/6e6ea7cf-b68b-46e4-a547-14ca823ea3db
-- title:
--   Triangular: classical carleson
-- statement:
--   **Carleson's theorem** for continuous functions. The Fourier series of a continuous
--   1-periodic function converges pointwise almost everywhere.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Theorems.lean#L35-L37
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Theorems.lean#L35-L37

module
public import Definitions.Def_Triangular_Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Definitions.Def_Triangular_Auto_Carleson
public import Definitions.Def_Triangular_Theorems
public import Theorems.Thm_Auto_classical_carleson

set_option autoImplicit true
@[expose] public section
public section
open Triangular
open MeasureTheory SchwartzMap Topology Filter Function

theorem Triangular.classical_carleson (f : ℝ → ℂ) (hf : Continuous f) (hper : Periodic f 1) :
    ∀ᵐ x, Tendsto (fun N ↦ fourierPartialSum f N x) atTop (𝓝 (f x)) := by sorry
