-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_depth_hierarchy
-- name    : SymmetricDepthHierarchy.ConstantDepth.depth_hierarchy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:33.366531+00:00
-- url     : https://prove2.me/theorems/9c383f9d-72a3-4133-9cc5-07a4d98c8aea
-- title:
--   Theorem 3.1: support depth $\Delta$ needs orbit size $n^{\log_2 n-\Delta\log_2\log_2 n-3}$ for $\mathrm{hom}_{T_{\Delta,n},n}$, while support depth $\Delta+1$ achieves $13n^{\Delta+2}$
-- statement:
--   Let $\Delta\ge1$ and $n\ge20$, let $K$ be a field of characteristic zero, and let $T_{\Delta,n}$ be the full $n$-ary tree of depth $\Delta$, viewed as a pattern with the root on the left side.
--
--   1. Every matrix-symmetric circuit over $X_n$ of support depth $\le\Delta$ computing $\mathrm{hom}_{T_{\Delta,n},n}$ has orbit size, and hence size, at least
--   $$n^{\log_2 n-\Delta\log_2\log_2 n-3}.$$
--   2. There is a matrix-symmetric circuit of support depth $\Delta+1$, depth $2\Delta+3$, orbit size $\le n^2$ and size $\le 13n^{\Delta+2}$ computing $\mathrm{hom}_{T_{\Delta,n},n}$.
--
--   For fixed $\Delta$ the size gap between support depth $\Delta$ and $\Delta+1$ is $n^{(1-o(1))\log_2 n}$, a strict quasipolynomial constant-depth hierarchy for matrix-symmetric circuits.
--
--   **Formalization Note.** The lower bound is a real power of $n$ (no rounding); the exponent may be nonpositive for small $n$. Support depth and depth in clause 2 are exact values.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, variables x_{i,j} → Fin n (0-based), variables indexed by Fin n × Fin n; reason: relabelling of [n]; the same polynomials and circuits
--   - reading: T_{Δ,n} as a pattern (bipartition not specified) → left side: words of even length (the root); right side: words of odd length; reason: the natural 2-colouring of a tree; the other choice gives the transposed polynomial, for which the statement is the same by the symmetry x_{i,j} ↦ x_{j,i}
--   - encoding: T_{Δ,k}: the full k-ary tree of depth Δ → vertices: words of length 0,…,Δ over Fin k (Σ j : Fin (Δ+1), List.Vector (Fin k) j), each word adjacent to its one-letter extensions; reason: the standard model of the full k-ary tree of depth Δ
--   - encoding: S supports g if the pointwise stabiliser Stab•(S) ≤ Γ_n fixes g (C rigid) → every automorphism extending an element of the pointwise stabiliser of S fixes g; reason: for a rigid circuit each element has exactly one extension, so the two agree; supports are only applied to reduced (hence rigid, Lemma 2.3) circuits or to rigidifications
--   - reading: sup(g): the unique minimal support, 'contained in every support of g' → sup(g) := intersection of all supports with fewer than n/2 points on each side; reason: containment in every support is false for large supports (n = 20, the reduced circuit summing all 400 variables: {L1,R1} and {L2,…,L20,R1} both support x_{1,1}); by [DPS26a, Lemmas 2.1, 2.2] the intersection of the small supports is the unique minimal small support, the only object the source's later arguments use
--   - reading: height of a gate: maximal number of wires on a path from it to an input gate (Appendix A); undefined for gates with no path to an input → height: length of a longest downward path (to any gate without children); reason: the two agree whenever every internal gate has a child; with the literal definition, childless internal gates (empty sums/products) have no height and the rigidification would be undefined or would merge gates computing 0 and 1
--   - encoding: depth: maximum number of wires on an input-to-output path → depth = that maximum, read as 0 when no input-to-output path exists; reason: the maximum of the empty set occurs only for circuits without input gates
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 9 (PDF p. 12), Theorem 3.1; proof in §B.5, pp. 40–41 (PDF pp. 43–44)

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Circuit
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Support
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Rigidification
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Theorem 3.1, printed p. 9 (PDF p. 12). Let `Δ ≥ 1` and `n ≥ 20`, and let `T_{Δ,n}` be the full
`n`-ary tree of depth `Δ`.
1. Every matrix-symmetric circuit of support depth `≤ Δ` computing `hom_{T_{Δ,n},n}` has orbit
   size, and hence size, at least `n^{log₂ n − Δ log₂ log₂ n − 3}`.
2. There is a matrix-symmetric circuit of support depth `Δ + 1`, depth `2Δ + 3`, orbit size `≤ n²`,
   and size `≤ 13 n^{Δ+2}` computing `hom_{T_{Δ,n},n}`. -/
theorem depth_hierarchy {K : Type} [Field K] [CharZero K] (Δ n : ℕ) (hΔ : 1 ≤ Δ)
    (hn : 20 ≤ n) :
    (∀ (V : Type) [Fintype V] (C : Circuit K n V), C.WellFormed → C.MatrixSymmetric →
        C.supportDepth ≤ Δ → C.Computes ((treePattern Δ n).homPoly K n) →
        (n : ℝ) ^ (Real.logb 2 n - Δ * Real.logb 2 (Real.logb 2 n) - 3) ≤ (C.maxOrb : ℝ) ∧
        (n : ℝ) ^ (Real.logb 2 n - Δ * Real.logb 2 (Real.logb 2 n) - 3) ≤ (C.size : ℝ)) ∧
    (∃ (V : Type) (_ : Fintype V) (C : Circuit K n V),
        C.WellFormed ∧ C.MatrixSymmetric ∧ C.supportDepth = Δ + 1 ∧ C.depth = 2 * Δ + 3 ∧
        C.maxOrb ≤ n ^ 2 ∧ C.size ≤ 13 * n ^ (Δ + 2) ∧
        C.Computes ((treePattern Δ n).homPoly K n)) := by sorry

end SymmetricDepthHierarchy.ConstantDepth
