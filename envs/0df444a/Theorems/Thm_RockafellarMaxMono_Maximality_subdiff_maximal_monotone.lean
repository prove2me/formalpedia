-- Prove2me | Theorems.Thm_RockafellarMaxMono_Maximality_subdiff_maximal_monotone
-- name    : RockafellarMaxMono.Maximality.subdiff_maximal_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:06:24.32886+00:00
-- url     : https://prove2.me/theorems/755110c6-3838-4555-b50c-b3adb96416fa
-- title:
--   Theorem A — the subdifferential of a lsc proper convex function on a Banach space is maximal monotone
-- statement:
--   Let $E$ be a real Banach space with dual $E^*$. If $f$ is a lower semicontinuous proper convex function on $E$, then its subdifferential
--
--   $$
--   \partial f : E \to E^*, \qquad \partial f(x) = \{\, x^* \in E^* \mid f(y) \ge f(x) + \langle y - x, x^* \rangle \ \forall y \in E \,\},
--   $$
--
--   is a maximal monotone operator: it is monotone, and its graph is not properly contained in the graph of any other monotone operator from $E$ to $E^*$.
--
--   This is Rockafellar's Theorem A. It makes subdifferentials of closed proper convex functions a fundamental example in the theory of maximal monotone operators, and it holds in every real Banach space, reflexive or not.
--
--   **Formalization Note** $f$ takes values in `EReal`, never $-\infty$ and not identically $+\infty$; lower semicontinuity is for the norm topology of $E$ (equivalent to weak lower semicontinuity for convex $f$). Maximality compares $\partial f$ with every monotone operator `E → Set (StrongDual ℝ E)` whose graph contains that of $\partial f$. No reflexivity, inner product or finite dimension is assumed.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 210, Theorem A

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Maximality_MonotoneOperator

namespace RockafellarMaxMono.Maximality

theorem subdiff_maximal_monotone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    IsMaximalMonotone (Shared.subdiff f) := by sorry

end RockafellarMaxMono.Maximality
