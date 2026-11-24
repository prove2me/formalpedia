-- Prove2me | Theorems.Thm_SensitivityLowPacking_residual_zero_bound
-- name    : SensitivityLowPacking.residual_zero_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:21.146863+00:00
-- url     : https://prove2.me/theorems/e43a1d9e-ae88-433c-a0b4-b7a389226a6e
-- title:
--   Conditioning bounds the remaining zero population
-- statement:
--   Let $V$ be finite, let $D$ be a directed relation, and assign nonnegative integer multiplicities $n_v$ and base costs $b_v$. Write $o_v=\sum_{w\in V:D(v,w)}n_w$. Assume every occupied vertex satisfies $n_v+2(b_v+o_v)\le3$. A designated zero set $Z$ consists of occupied vertices with $n_v\le2$ and $b_v+o_v=0$. Fix a set $F\subseteq V$ of assigned vertices. Put $b'_v=b_v+\sum_{w\in F:D(v,w)}n_w$. Let $U$ be the live candidates: unassigned vertices with $b'_v\le1$ such that adding one copy at $v$ would preserve the budget of every occupied fixed predecessor. Let $Z_F=\{v\in F:0<n_v\le2,\ b'_v=0\}$. Suppose every edge-free subset of $\{v\in U:b'_v=0\}$ has size at most $\alpha$. Then
--
--   $$|Z|\le|Z_F|+\alpha.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/LowPackingResidual.lean lines 141–176; SHA256 9462682cea40addd8b31518ac1b7573598350c02319b958a9868c1d396528a14; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

theorem SensitivityLowPacking.residual_zero_bound (D : V → V → Prop) (vertices fixed zeros : Finset V)
    (count base : V → ℕ) (hf : fixed ⊆ vertices)
    (hbudget : ∀ v ∈ vertices, 0 < count v →
      count v + 2 * (base v + weightedOut D vertices count v) ≤ 3)
    (hzsub : zeros ⊆ Support vertices count) (hzsmall : ∀ v ∈ zeros, count v ≤ 2)
    (hz : ∀ v ∈ zeros, base v + weightedOut D vertices count v = 0)
    (alpha : ℕ)
    (hcap : ∀ s ⊆ (liveCandidates D vertices fixed count base).filter
        (fun v => fixedBase D fixed count base v = 0),
      (∀ v ∈ s, ∀ w ∈ s, ¬D v w) → s.card ≤ alpha) :
    zeros.card ≤ (fixedZeros D fixed count base).card + alpha := by sorry
