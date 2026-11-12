-- Prove2me | Theorems.Thm_WatrousTQI_unital_channels_compact_convex
-- name    : WatrousTQI.unital_channels_compact_convex
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-11T22:56:21.200975+00:00
-- url     : https://prove2.me/theorems/f3b2ab26-abad-4fce-804a-4122c32bd412
-- title:
--   Theorem 4.23 proof — compact convex geometry of unital channels
-- statement:
--   For every positive integer $d$, the set of all trace-preserving completely positive maps on complex $d\times d$ matrices that fix $I_d$ is compact and real convex, and its real linear span is finite-dimensional. The ambient maps are unbundled functions with the pointwise topology inherited from matrices. On complex-linear maps this agrees with the usual finite-dimensional operator-space topology. The finite-span clause records explicitly the finite-dimensional setting used by the source.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Chapter 4. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; Proof of Theorem 4.23, first paragraph, printed p.227 (PDF p.235), using the finite-dimensional space of superoperators and Theorem 1.10.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WatrousTQI_UnitalChannels
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate BigOperators

namespace WatrousTQI

theorem unital_channels_compact_convex (d : ℕ) (hd : 0 < d) :
    IsCompact (unitalChannels d) ∧ Convex ℝ (unitalChannels d) ∧
      FiniteDimensional ℝ (Submodule.span ℝ (unitalChannels d)) := by sorry

end WatrousTQI
