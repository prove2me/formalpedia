-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_negRev_timeChange
-- name    : WhittFLT.TimeReversal.negRev_timeChange
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:02.927104+00:00
-- url     : https://prove2.me/theorems/3a6628df-0a9c-4771-99fe-3a9ee9ff5e92
-- title:
--   Reflected time changes preserve Λ and fix the identity
-- statement:
--   Let $\Lambda$ be the increasing homeomorphisms of $[0,1]$, and for $\lambda\in\Lambda$ define $(-r)(\lambda)(t)=1-\lambda(1-t)$. Then
--
--   $$
--   (-r)(\lambda)\in\Lambda,\qquad (-r)(e)=e,
--   $$
--
--   where $e(t)=t$. This identifies the time changes available after reversing a path.
--
--   **Formalization Note** An element of $\Lambda$ is encoded by strict increase, continuity, and surjectivity on $[0,1]$; all values outside that interval are irrelevant.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §8, proof of Theorem 8.1, p. 84; https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Reversal

namespace WhittFLT.TimeReversal

open Set

/-- §8, proof of Theorem 8.1, p. 84: reflected time changes belong to Λ and fix the identity. -/
theorem negRev_timeChange (l : ℝ → ℝ) (hl : WhittFLT.Composition.IsTimeChange 0 1 l) :
    WhittFLT.Composition.IsTimeChange 0 1 (negRev l) ∧ EqOn (negRev id) id (Set.Icc 0 1) := by sorry

end WhittFLT.TimeReversal
