-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_A_1
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:11:06.188401+00:00
-- url     : https://prove2.me/theorems/d85e5d21-d56e-4c02-923b-47a2af304ea5
-- title:
--   Theorem A.1 — Small-index subgroups contain an alternating pointwise stabilizer
-- statement:
--   Let n>=9, let 1<=r<=n/2, and let H be a subgroup of the permutation group on [n]. Here Alt(T) consists of even permutations fixing every point of T, rather than permutations supported on T. This statement is independent of a field.
--
--   $$
--   [\mathrm{Sym}_n:H]<\min\{\tfrac12\binom n{\lfloor n/2\rfloor},\binom nr\}\ \Longrightarrow\ \exists T,\ |T|<r,\ \operatorname{Alt}(T)\le H.
--   $$
--
--   This is a companion theorem; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
--   - encoding: index less than half the central binomial coefficient and less than binom(n,r) → 2*index < binom(n,n/2) and index < binom(n,r), in natural numbers; reason: doubling preserves the strict rational-half threshold exactly, including an odd central coefficient; the conclusion explicitly quantifies even permutations fixing T pointwise
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 27 (PDF p. 30), Theorem A.1; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem theorem_A_1 (n r : ℕ) (hn : 9 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n/2)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hcentral : 2 * H.index < n.choose (n/2)) (hindex : H.index < n.choose r) :
    ∃ T : Finset (Fin n), T.card < r ∧
      ∀ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = 1 →
        (∀ i ∈ T, σ i = i) → σ ∈ H := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
