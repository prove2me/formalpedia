-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_revTime_comp_negRev
-- name    : WhittFLT.TimeReversal.revTime_comp_negRev
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:22.370482+00:00
-- url     : https://prove2.me/theorems/489f95b5-b9ae-4f4f-924e-537fa043e608
-- title:
--   Time reversal intertwines reflected time changes
-- statement:
--   Let $x\in D$ and $\lambda\in\Lambda$. With $(-r)(\lambda)(t)=1-\lambda(1-t)$, the reversal identities on $[0,1]$ are
--
--   $$
--   R(x)\circ(-r)(\lambda)=R(x\circ\lambda),\qquad
--   r(x)\circ(-r)(\lambda)=r(x\circ\lambda).
--   $$
--
--   They compare a time change applied after reversal with reversal applied after a time change.
--
--   **Formalization Note** The paper prints the second identity for $x\in D_\theta$; it also holds for all $x\in D$ because $\lambda(1)=1$, so the Lean statement uses $D$. Paths are total functions and the equality is restricted to $[0,1]$. The group is additive and commutative, and its metric is translation invariant.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §8, proof of Theorem 8.1, p. 84; https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Reversal

namespace WhittFLT.TimeReversal

open Set

/-- §8, proof of Theorem 8.1, p. 84: reversal intertwines every time change with its reflection. -/
theorem revTime_comp_negRev {S : Type*} [AddCommGroup S] [MetricSpace S] [CompleteSpace S]
    [TopologicalSpace.SeparableSpace S] (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b)
    (x : ℝ → S) (hx : InD x) (l : ℝ → ℝ) (hl : WhittFLT.Composition.IsTimeChange 0 1 l) :
    EqOn (revTime x ∘ negRev l) (revTime (x ∘ l)) (Set.Icc 0 1) ∧
      EqOn (revTime0 x ∘ negRev l) (revTime0 (x ∘ l)) (Set.Icc 0 1) := by sorry

end WhittFLT.TimeReversal
