-- Prove2me | Theorems.Thm_SensitivityLowPacking_exists_packing_cover
-- name    : SensitivityLowPacking.exists_packing_cover
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T20:19:17.648337+00:00
-- url     : https://prove2.me/theorems/8c7c69de-538a-4d34-899a-959fc4ab6278
-- title:
--   A three-palette cover for feasible low-one multiplicities
-- statement:
--   Let $V$ be finite, let $D$ be irreflexive, and assign nonnegative integers $n_v,b_v$ satisfying
--
--   $$n_v>0\Rightarrow n_v+2\left(b_v+\sum_{w\in V:D(v,w)}n_w\right)\le3.$$
--
--   Let $Z$ be a designated set with multiplicity at most two and zero base-plus-outgoing load at its vertices. Put $w_v=2$ if $b_v=0$ and $w_v=1$ otherwise. There are palettes $P(v)\subseteq\{0,1,2\}$, disjoint along every directed edge between occupied vertices, such that
--
--   $$2\bigl(n_v+\mathbf1_{v\in Z}\bigr)\le |P(v)|w_v$$
--
--   at every occupied vertex.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/LowPackingColorCover.lean lines 40–97; SHA256 a33531b06c6583601f88bbc4b87179bb954f35a9753332e165888419a6eefa09; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

theorem SensitivityLowPacking.exists_packing_cover (D : V → V → Prop) (vertices zeros : Finset V)
    (count base : V → ℕ) (hirr : ∀ v, ¬D v v)
    (hbudget : ∀ v ∈ vertices, 0 < count v →
      count v + 2 * (base v + weightedOut D vertices count v) ≤ 3)
    (hzsmall : ∀ v ∈ zeros, count v ≤ 2)
    (hz : ∀ v ∈ zeros, base v + weightedOut D vertices count v = 0) :
    ∃ colors : V → Finset (Fin 3),
      (∀ v ∈ Support vertices count, ∀ w ∈ Support vertices count,
        D v w → Disjoint (colors v) (colors w)) ∧
      (∀ v ∈ Support vertices count,
        2 * (count v + if v ∈ zeros then 1 else 0) ≤ (colors v).card * packingWeight base v) := by sorry
