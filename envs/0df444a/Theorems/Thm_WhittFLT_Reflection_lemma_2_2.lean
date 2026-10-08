-- Prove2me | Theorems.Thm_WhittFLT_Reflection_lemma_2_2
-- name    : WhittFLT.Reflection.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:32.499332+00:00
-- url     : https://prove2.me/theorems/707ab1d9-ebcd-4cba-8f92-a4c93eeae744
-- title:
--   Lemma 2.2 — splitting J₁ convergence at a continuity point
-- statement:
--   Let $a<b<c$, let $x_n,x\in D([a,c],S)$, and suppose $x$ is continuous at $b$. Then convergence on the full interval is equivalent to convergence on both restrictions:
--
--   $$
--   x_n\to x\text{ in }D([a,c])\quad\Longleftrightarrow\quad x_n\to x\text{ in }D([a,b])\text{ and }x_n\to x\text{ in }D([b,c]),
--   $$
--   with each convergence in the $J_1$ topology. This lets local arguments be assembled across a continuity point.
--
--   **Formalization Note** The printed statement has “convergence” and a lowercase “d” in the final line; these are read as “converge” and $D([a,b])$. The paths are total functions on $\mathbb R$, and the source’s topological convergence is written sequentially.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Lemma 2.2, p. 71

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.Reflection

open Set Filter Topology

/-- Whitt (1980), Lemma 2.2, p. 71. -/
theorem lemma_2_2 {S : Type*} [MetricSpace S] (a b c : ℝ) (hab : a < b) (hbc : b < c)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (hxs : ∀ n, WhittFLT.Composition.IsCadlagOn (Icc a c) (xs n))
    (hx : WhittFLT.Composition.IsCadlagOn (Icc a c) x) (hb : ContinuousAt x b) :
    WhittFLT.Composition.J1TendstoOn a c xs x ↔ (WhittFLT.Composition.J1TendstoOn a b xs x ∧ WhittFLT.Composition.J1TendstoOn b c xs x) := by sorry

end WhittFLT.Reflection
