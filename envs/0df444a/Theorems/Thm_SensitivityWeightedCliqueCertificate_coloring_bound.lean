-- Prove2me | Theorems.Thm_SensitivityWeightedCliqueCertificate_coloring_bound
-- name    : SensitivityWeightedCliqueCertificate.coloring_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:29.286711+00:00
-- url     : https://prove2.me/theorems/3d839889-fa86-4fe6-a745-91f79ca5e9aa
-- title:
--   A weighted clique is bounded by the sum of color-class maxima
-- statement:
--   Let a bit-encoded adjacency relation be equipped with nonnegative integer vertex weights. Suppose a finite list of vertex classes passes the independence check in each class and covers a finite clique $K$. For each class $C$, let $m(C)$ be its maximum vertex weight, with $m(\varnothing)=0$. Then
--
--   $$\sum_{v\in K}w(v)\le\sum_C m(C).$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/WeightedCliqueCertificate.lean lines 24–69; SHA256 72037be65f9252ea0e5fab90db142b411b84bef23fde2c287be9bddd815bedc9; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CliqueCertificate
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_WeightedCliqueCertificate
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Bitwise

namespace SensitivityCliqueCertificate
end SensitivityCliqueCertificate
namespace SensitivityWeightedCliqueCertificate
end SensitivityWeightedCliqueCertificate


/-! The same explicit branch/coloring proof objects with nonnegative vertex weights. -/
open SensitivityWeightedCliqueCertificate
open scoped BigOperators
open SensitivityCliqueCertificate
set_option autoImplicit false

theorem SensitivityWeightedCliqueCertificate.coloring_bound (adj weight : ℕ → ℕ) (classes : List (List ℕ))
    (hgood : ∀ group ∈ classes, independentCheck adj group = true)
    (vertices : Finset ℕ) (hclique : Clique adj vertices)
    (hcover : ∀ v ∈ vertices, v ∈ classes.flatten) :
    (∑ v ∈ vertices, weight v) ≤ (classes.map (classFee weight)).sum := by sorry
