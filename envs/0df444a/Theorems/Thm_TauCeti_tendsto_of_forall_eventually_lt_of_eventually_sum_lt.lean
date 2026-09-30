-- Prove2me | Theorems.Thm_TauCeti_tendsto_of_forall_eventually_lt_of_eventually_sum_lt
-- name    : TauCeti.tendsto_of_forall_eventually_lt_of_eventually_sum_lt
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:42.668436+00:00
-- url     : https://prove2.me/theorems/677023ea-9ef1-4404-985c-822013526695
-- title:
--   Saturated lower bounds determine the individual limits
-- statement:
--   Let $\mathbb k$ be a linearly ordered field with its order topology, let $\mathcal F$ be a filter on a set $X$, and let $S$ be a finite index set. For $i\in S$, let $f_i:X\to\mathbb k$ and $c_i\in\mathbb k$. Suppose each inequality $b<f_i(x)$ holds eventually along $\mathcal F$ whenever $b<c_i$. Suppose also that
--
--   $$
--   \sum_{i\in S}f_i(x)<b\quad\text{eventually along }\mathcal F
--   \qquad\text{for every }b>\sum_{i\in S}c_i.
--   $$
--
--   Then for every $i\in S$,
--
--   $$
--   \lim_{x\to\mathcal F}f_i(x)=c_i.
--   $$
--
--   This identifies individual limits when their lower bounds exhaust an upper bound on their finite sum.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Topology/Algebra/Order/LiminfLimsup.lean#L47-L77) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Topology/Algebra/Order/LiminfLimsup.lean#L47-L77

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Lower bounds that saturate a limit of the sum are limits

Let `f i` be a finite family of functions into a linearly ordered field. If every `f i` is
eventually above each value below `c i`, so that `c i` is a lower bound for its lower limit, and
the sum `∑ i, f i` is eventually below each value above `∑ i, c i`, then every `f i` tends to
`c i`: the lower bounds of the other members leave room for no more than `c i` in the sum.

The two hypotheses are the two halves of `tendsto_order`, the lower half for each member and the
upper half for the sum. No boundedness is assumed, so the statement avoids the side conditions of
`Filter.liminf` and `Filter.limsup`.

This is how a one-sided estimate becomes an asymptotic: an argument that exhibits enough mass in
each member of a finite partition, and cannot see that there is no more, still determines every
member once the total is known.

The analogous Dirichlet-density squeeze is
`NumberField.Set.hasDirichletDensity_of_squeeze`.

## Main results

* `TauCeti.tendsto_of_forall_eventually_lt_of_eventually_sum_lt`: lower bounds on the members of
  a finite family whose sum is bounded above by the sum of the bounds are limits.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Filter Topology

theorem TauCeti.tendsto_of_forall_eventually_lt_of_eventually_sum_lt {ι α 𝕜 : Type*} [_root_.Field 𝕜]
    [_root_.LinearOrder 𝕜] [_root_.IsStrictOrderedRing 𝕜] [_root_.TopologicalSpace 𝕜] [_root_.OrderTopology 𝕜]
    {l : _root_.Filter α} {s : _root_.Finset ι} {f : ι → α → 𝕜} {c : ι → 𝕜}
    (hlow : ∀ i ∈ s, ∀ b < c i, ∀ᶠ x in l, b < f i x)
    (hsum : ∀ b > ∑ i ∈ s, c i, ∀ᶠ x in l, ∑ i ∈ s, f i x < b) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    _root_.Filter.Tendsto (f i₀) l (𝓝 (c i₀)) := by sorry
