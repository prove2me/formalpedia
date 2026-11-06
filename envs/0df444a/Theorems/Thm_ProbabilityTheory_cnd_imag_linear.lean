-- Prove2me | Theorems.Thm_ProbabilityTheory_cnd_imag_linear
-- name    : ProbabilityTheory.cnd_imag_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:53:42.303393+00:00
-- url     : https://prove2.me/theorems/f58a0876-7090-4aea-8711-403b577c1fa3
-- title:
--   LeanLevy: ProbabilityTheory.cnd_imag_linear
-- statement:
--   The imaginary linear function `ξ ↦ a·ξ·I` is conditionally negative definite: Exact extracted Lean theorem type; proof pending Prove2Me verification. Bochner source-module import replaced by its exact public theorem interface; that theorem's proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L353

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Probability_Characteristic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

theorem ProbabilityTheory.cnd_imag_linear : ∀ (a : Real),
  ProbabilityTheory.IsConditionallyNegativeDefinite fun ξ =>
    @HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
      (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) ↑a ↑ξ) Complex.I := by sorry
