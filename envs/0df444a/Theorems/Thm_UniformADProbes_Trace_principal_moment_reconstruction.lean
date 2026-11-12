-- Prove2me | Theorems.Thm_UniformADProbes_Trace_principal_moment_reconstruction
-- name    : UniformADProbes.Trace.principal_moment_reconstruction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:05.19838+00:00
-- url     : https://prove2.me/theorems/aa054132-272a-4134-a393-20d8be7042aa
-- title:
--   Theorem 3.1 — Principal-moment reconstruction
-- statement:
--   Let $T,T'$ be finite nonempty connected simple trees, possibly of different orders. Let $A_T,D_T$ be their adjacency and actual diagonal degree matrices, and let $\mathbf1$ denote the all-ones vector. If
--   $$\mathbf1^Tw(A_T,D_T)\mathbf1=\mathbf1^Tw(A_{T'},D_{T'})\mathbf1
--   \qquad\text{for every }w\in\{x,y\}^*,$$
--   then $T\cong T'$.
--
--   The empty word is included, so equality of moments itself records the order. This is the graph reconstruction input restated in the supplied paper from LL26, Theorem 5.4; it is a theorem target, not an assumed reconstruction principle.
--
--   Differences from the source:
--   - encoding: finite nonempty trees and principal moments → trees on Fin n and Fin m, with principal moments as integer sums of all word-matrix entries; reason: labelling transports every finite tree; the all-ones bilinear form is exactly the sum, and integer equality agrees with real equality
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), Theorem 3.1, p. 7 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false

namespace UniformADProbes.Trace

theorem principal_moment_reconstruction (n m : ℕ)
    (T : SimpleGraph (Fin n)) (T' : SimpleGraph (Fin m))
    (hT : T.IsTree) (hT' : T'.IsTree)
    (hmom : ∀ w : Word,
      (∑ i, ∑ j, wordEval (adjacency T) (degreeMatrix T) w i j) =
      (∑ i, ∑ j, wordEval (adjacency T') (degreeMatrix T') w i j)) :
    Nonempty (T ≃g T') := by sorry

end UniformADProbes.Trace
