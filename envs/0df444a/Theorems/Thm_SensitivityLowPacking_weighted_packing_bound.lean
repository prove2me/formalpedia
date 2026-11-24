-- Prove2me | Theorems.Thm_SensitivityLowPacking_weighted_packing_bound
-- name    : SensitivityLowPacking.weighted_packing_bound
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:19:17.753839+00:00
-- url     : https://prove2.me/theorems/f90905e8-12f5-40ff-941a-72ea34feecc6
-- title:
--   Weighted independence bounds the total low-one packing score
-- statement:
--   Let $V$ be finite, let $D$ be a directed relation, and assign nonnegative integer multiplicities $n_v$ and base costs $b_v$. Write $o_v=\sum_{w\in V:D(v,w)}n_w$. Assume every occupied vertex satisfies $n_v+2(b_v+o_v)\le3$. A designated zero set $Z$ consists of occupied vertices with $n_v\le2$ and $b_v+o_v=0$. Assume $D$ is irreflexive, and give vertex $v$ weight $w_v=2$ when $b_v=0$ and weight $1$ otherwise. If every subset with no directed edge has total weight at most $\alpha$, then
--
--   $$2\left(\sum_{v\in V}n_v+|Z|\right)\le3\alpha.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/LowPackingColorCover.lean lines 99–136; SHA256 a33531b06c6583601f88bbc4b87179bb954f35a9753332e165888419a6eefa09; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingCliqueBounds
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingColorCover
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

namespace SensitivityLowPacking
end SensitivityLowPacking
namespace SensitivityPseudoforest
end SensitivityPseudoforest


/-! Weighted independent-set certificates control all low-one multiplicities. -/
open SensitivityLowPacking
open scoped Classical BigOperators
open SensitivityPseudoforest
set_option autoImplicit false
variable {V : Type} [DecidableEq V]

theorem SensitivityLowPacking.weighted_packing_bound (D : V → V → Prop) (vertices zeros : Finset V)
    (count base : V → ℕ) (hirr : ∀ v, ¬D v v)
    (hbudget : ∀ v ∈ vertices, 0 < count v →
      count v + 2 * (base v + weightedOut D vertices count v) ≤ 3)
    (hzsub : zeros ⊆ Support vertices count) (hzsmall : ∀ v ∈ zeros, count v ≤ 2)
    (hz : ∀ v ∈ zeros, base v + weightedOut D vertices count v = 0)
    (alpha : ℕ)
    (hcap : ∀ s ⊆ vertices, (∀ v ∈ s, ∀ w ∈ s, ¬D v w) →
      (∑ v ∈ s, packingWeight base v) ≤ alpha) :
    2 * ((∑ v ∈ vertices, count v) + zeros.card) ≤ 3 * alpha := by sorry
