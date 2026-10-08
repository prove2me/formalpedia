-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_revTime_mem
-- name    : WhittFLT.TimeReversal.revTime_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:19.123741+00:00
-- url     : https://prove2.me/theorems/febf7d5e-041d-436b-bf0d-54d7cbdd15a3
-- title:
--   Time reversal maps the path spaces to themselves
-- statement:
--   Let $S$ be a complete separable additive metric group with translation-invariant metric. For $x\in D$, the reverse path $R(x)$ belongs to $D$, and the shifted reverse path $r(x)$ belongs to $D_\theta$. On $[0,1]$,
--
--   $$
--   R(R(x))=x;\qquad x\in D_\theta\ \Longrightarrow\ r(r(x))=x.
--   $$
--
--   These identities make $R:D\to D$ and the restriction $r:D_\theta\to D_\theta$ bijections, supplying the well-defined maps used in the metric theorem.
--
--   **Formalization Note** The paper calls the maps one-to-one and onto in its proof. The unrestricted $r:D\to D_\theta$ loses the initial offset and is not injective; the involution statement therefore applies to its restriction to $D_\theta$. Equality of total Lean functions is asserted only on $[0,1]$. The group is formalized as additive and commutative, and $D$ includes $x(1)=x(1-)$.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §8, p. 83 and proof of Theorem 8.1, p. 84; https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Reversal

namespace WhittFLT.TimeReversal

open Set

/-- §8, pp. 83–84: reversal preserves D, shifted reversal lands in Dθ, and each reversal is
an involution on its natural domain. -/
theorem revTime_mem {S : Type*} [AddCommGroup S] [MetricSpace S] [CompleteSpace S]
    [TopologicalSpace.SeparableSpace S] (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b)
    (x : ℝ → S) (hx : InD x) :
    InD (revTime x) ∧ InDθ (revTime0 x) ∧
      EqOn (revTime (revTime x)) x (Set.Icc 0 1) ∧
      (x 0 = 0 → EqOn (revTime0 (revTime0 x)) x (Set.Icc 0 1)) := by sorry

end WhittFLT.TimeReversal
