-- Prove2me | Theorems.Thm_ProfiniteMeasure_ext_of_clopen_masses
-- name    : ProfiniteMeasure.ext_of_clopen_masses
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T05:28:02.499501+00:00
-- url     : https://prove2.me/theorems/fa40f0e8-4ef0-4ab4-9e28-8880cd7ee2ff
-- title:
--   Abstract measures on profinite spaces are determined by clopen masses
-- statement:
--   Let X be a compact Hausdorff totally disconnected space and let R be a normed field. Two continuous R-linear functionals on C(X,R) are equal if they agree on the characteristic function of every clopen subset of X. This gives the uniqueness mechanism for extending bounded p-adic residue-disk masses to abstract measures, as required by the Colmez moment-extension frontier of the Mazur–Tate–Teitelbaum interpolation mission.
-- source:
--   Standard density argument using finite clopen approximations. Supporting result for PadicMeasure.colmez_r0_moment_extension in the mission Ordinary p-adic L-functions: Mazur–Tate–Teitelbaum interpolation.

import Mathlib.NumberTheory.Padics.Measure.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set Filter UniformSpace ContinuousMap TopologicalSpace

theorem ProfiniteMeasure.ext_of_clopen_masses {X R : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [NormedField R]
    (μ ν : AbstractMeasure X R R)
    (h : ∀ U : Clopens X,
      μ ⟨(U : Set X).indicator (fun _ => (1 : R)),
        U.isClopen.continuous_indicator continuous_const⟩ =
      ν ⟨(U : Set X).indicator (fun _ => (1 : R)),
        U.isClopen.continuous_indicator continuous_const⟩) : μ = ν := by sorry
