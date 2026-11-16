-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_theorem_4_3
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:59:16.578392+00:00
-- url     : https://prove2.me/theorems/f06a1a59-c5b2-44dd-8734-73185cb0466a
-- title:
--   Theorem 4.3 — Depth reduction with superpolynomial orbit size
-- statement:
--   Let K have characteristic zero, let epsilon>0, and let p_n be matrix-invariant polynomials of degree at most d(n), with d,s natural-valued. Suppose every positive n admits a symmetric circuit of orbit at most s(n), where s(n)<=2^(n^(1-epsilon)). For all sufficiently large n the following two bounds hold for the same new circuit. All epsilon>0 are included, and degrees zero and one remain allowed.
--
--   $$
--   \operatorname{depth}(C_n)\le4\left\lceil\log_{5/4}(4\max\{1,d(n)\})\right\rceil+4,\qquad\operatorname{maxOrb}(C_n)\le\max\{s(n),n^2\}^{3/\varepsilon}.
--   $$
--
--   This is a companion theorem; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
--   - reading: depth O(log d(n)), with the proof bound 4 ceil(log_(5/4)(4d))+4 for nonconstant polynomials → depth at most 4 ceil(log_(5/4)(4 max(1,d(n))))+4, keeping d=0 and d=1; reason: the proof supplies this explicit bound; constants have depth zero, while literal log(1)=0 would incorrectly require depth-zero circuits for the invariant sum of all variables
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 12 (PDF p. 15), Theorem 4.3; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem theorem_4_3 (K : Type) [Field K] [CharZero K] (ε : ℝ) (hε : 0 < ε)
    (p : Family K) (d s : ℕ → ℕ) (hinv : invariantFamily p)
    (hdegree : ∀ n, 1 ≤ n → (p n).totalDegree ≤ d n)
    (hbound : ∀ n, 1 ≤ n → (s n : ℝ) ≤ Real.rpow 2 (Real.rpow n (1-ε)))
    (hcircuit : ∀ n, 1 ≤ n → hasCircuit n (p n) (fun C => C.maxOrb ≤ s n)) :
    ∃ N : ℕ, ∀ n, 1 ≤ n → N ≤ n →
      hasCircuit n (p n) (fun C =>
        C.depth ≤ 4 * ⌈Real.logb (5/4 : ℝ) (4 * (max 1 (d n) : ℕ))⌉₊ + 4 ∧
        (C.maxOrb : ℝ) ≤ Real.rpow (max (s n : ℝ) ((n : ℝ)^2)) (3/ε)) := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
