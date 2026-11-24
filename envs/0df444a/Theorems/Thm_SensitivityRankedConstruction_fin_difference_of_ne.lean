-- Prove2me | Theorems.Thm_SensitivityRankedConstruction_fin_difference_of_ne
-- name    : SensitivityRankedConstruction.fin_difference_of_ne
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:50:31.82453+00:00
-- url     : https://prove2.me/theorems/4ff95cd2-f1bf-4b0a-a3b0-ab65bdfd4113
-- title:
--   Opposite nonzero displacements in a finite cyclic group
-- statement:
--   Let $x,y\in\{0,\ldots,n-1\}$ be distinct and set
--   $$
--   d=(y+n-x)\bmod n.
--   $$
--   Then $0<d<n$, and the opposite displacement is
--   $$
--   (x+n-y)\bmod n=n-d.
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/TournamentGuardCoverage.lean lines 60–84; SHA256 3675980c0f9f9889be8fdab852de312c270299e594e366dcc6659f604fc6e08e; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Pairwise orientation gives the guard that separates strict row colors. -/
open SensitivityRankedConstruction
open SensitivityHighHeadGuardBridge

theorem SensitivityRankedConstruction.fin_difference_of_ne {n : ℕ} (x y : Fin n) (hne : x ≠ y) :
    0 < (y.val + n - x.val) % n ∧ (y.val + n - x.val) % n < n ∧
      (x.val + n - y.val) % n = n - (y.val + n - x.val) % n := by sorry
