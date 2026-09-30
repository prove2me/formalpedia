-- Prove2me | Theorems.Thm_TauCeti_NumberField_mixedEmbedding_volume_eq_two_pow_mul_volume_inter_pos
-- name    : TauCeti.NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_inter_pos
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:44:41.694632+00:00
-- url     : https://prove2.me/theorems/1df76281-2643-45a4-9790-6bf2d3504fdb
-- title:
--   Volume of a prescribed-sign region
-- statement:
--   Let $K$ be a number field and $V_K$ its Minkowski space, equipped with the standard volume measure. Let $S$ be a finite set of real places and let $A\subseteq V_K$ be measurable. Suppose $A$ is invariant under negating the coordinate at each place in $S$. Then
--
--   $$
--   \operatorname{vol}(A)=2^{|S|}\operatorname{vol}\bigl(A\cap\{x:x_w>0\text{ for every }w\in S\}\bigr).
--   $$
--
--   The equality holds for extended nonnegative volumes, without a finiteness assumption on $A$.
--
--   This accounts for positivity constraints at real places in archimedean volume calculations.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/CanonicalEmbedding/SignCut.lean#L82-L101) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/CanonicalEmbedding/SignCut.lean#L82-L101

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cutting a reflection-invariant subset of the mixed space at a finset of real places

Let `S` be a finset of real places and `A` a subset of the mixed space preserved by the reflection
`negAt {w}` of the real coordinate at each single place `w` of `S`.  The `2 ^ S.card` sign patterns
along `S` then cut `A` into pieces of equal volume, exhausting `A` up to the null set where some
coordinate of `S` vanishes.

Cutting `A` down to the points that are positive at every place of `S` therefore divides its
volume by `2 ^ S.card`, the real coordinates outside `S` staying free.  A set whose membership
depends on the real coordinates only through their absolute values is invariant at every real
place, and for `S` all of the real places the statement is then Mathlib's
`NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_plusPart`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.isOpen_setOfPred_forall_mem_pos`: the points positive at
  every place of a finset of real places form an open set.
* `TauCeti.NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_inter_pos`: for a set invariant
  under reflection at each place of `S`, the volume is `2 ^ S.card` times the volume of the part
  that is positive at every place of `S`.
-/

 section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding
end TauCeti.NumberField.mixedEmbedding
section TauCeti.NumberField.mixedEmbedding
open TauCeti TauCeti.NumberField TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]





open scoped Classical

theorem TauCeti.NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_inter_pos (S : _root_.Finset {w : _root_.NumberField.InfinitePlace K // w.IsReal})
    {A : _root_.Set (_root_.NumberField.mixedEmbedding.mixedSpace K)}
    (hA : ∀ w ∈ S, ∀ x : _root_.NumberField.mixedEmbedding.mixedSpace K, _root_.NumberField.mixedEmbedding.negAt ({w} : _root_.Set _) x ∈ A ↔ x ∈ A)
    (hm : _root_.MeasurableSet A) : _root_.MeasureTheory.MeasureSpace.volume A = 2 ^ S.card * _root_.MeasureTheory.MeasureSpace.volume (A ∩ {x | ∀ w ∈ S, 0 < x.1 w}) := by sorry
