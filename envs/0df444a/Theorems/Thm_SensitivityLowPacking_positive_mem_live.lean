-- Prove2me | Theorems.Thm_SensitivityLowPacking_positive_mem_live
-- name    : SensitivityLowPacking.positive_mem_live
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:21.125789+00:00
-- url     : https://prove2.me/theorems/7cbfdca7-3e13-4abd-ae66-0b54332cee05
-- title:
--   Every occupied unassigned vertex survives the live-candidate filter
-- statement:
--   Let $V$ be finite, $F\subseteq V$, and let multiplicities $n_v$ and base costs $b_v$ satisfy the low-one packing budget
--
--   $$n_v>0\Rightarrow n_v+2\left(b_v+\sum_{w\in V:D(v,w)}n_w\right)\le3.$$
--
--   Set $b'_v=b_v+\sum_{w\in F:D(v,w)}n_w$. Every $v\in V\setminus F$ with $n_v>0$ satisfies $b'_v\le1$ and
--
--   $$w\in F,\ n_w>0,\ D(w,v)\Rightarrow n_w+2(b'_w+1)\le3.$$
--
--   Consequently every occupied unassigned vertex is a live candidate.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/LowPackingResidual.lean lines 49–70; SHA256 9462682cea40addd8b31518ac1b7573598350c02319b958a9868c1d396528a14; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingCliqueBounds
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_LowPackingResidual
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


/-! Conditioning a low packing on a partial assignment preserves exact guard budgets. -/
open SensitivityLowPacking
open scoped Classical BigOperators
open SensitivityPseudoforest
set_option autoImplicit false
variable {V : Type} [DecidableEq V]

theorem SensitivityLowPacking.positive_mem_live (D : V → V → Prop) (vertices fixed : Finset V)
    (count base : V → ℕ) (hf : fixed ⊆ vertices)
    (hbudget : ∀ v ∈ vertices, 0 < count v →
      count v + 2 * (base v + weightedOut D vertices count v) ≤ 3)
    (v : V) (hv : v ∈ vertices \ fixed) (hp : 0 < count v) :
    v ∈ liveCandidates D vertices fixed count base := by sorry
