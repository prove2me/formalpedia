-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_bounded_forestwidth_circuit
-- name    : SymmetricDepthHierarchy.ConstantDepth.bounded_forestwidth_circuit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:29.407299+00:00
-- url     : https://prove2.me/theorems/fba67323-6a4e-492e-844e-da7ce0cdf143
-- title:
--   Theorem B.2: $\mathrm{hom}_{F,n}$ for $\mathrm{fw}_\Delta(F)\le k-1$ has a reduced matrix-symmetric circuit with five simultaneous bounds
-- statement:
--   Let $\Delta\ge1$, $k\ge2$ and $n\ge2k+1$, and let $F$ be a bipartite multigraph with $\mathrm{fw}_\Delta(F)\le k-1$. Then $\mathrm{hom}_{F,n}$ is computed by a reduced matrix-symmetric circuit $C$ with
--
--   1. support size $\le k$,
--   2. support depth $\le\Delta$,
--   3. orbit size $\le n^k$,
--   4. depth $\le 2\Delta+1$, and
--   5. size $\le 5n^k\bigl(|V(F)|+|E(F)|\bigr)+1$,
--
--   where $|E(F)|$ counts edges with multiplicity.
--
--   This is the upper-bound half of the characterisation and yields the upper clause of the depth hierarchy theorem.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, variables x_{i,j} → Fin n (0-based), variables indexed by Fin n × Fin n; reason: relabelling of [n]; the same polynomials and circuits
--   - encoding: fw_Δ(F) ≤ k − 1 (least k ≥ 0 with a decomposition) → forestwidth Δ F.graph + 1 ≤ k in ℕ∞ (fw = ⊤ if no decomposition exists); reason: avoids truncated subtraction; for Δ ≥ 1 every finite graph has a decomposition, so fw is the source's finite minimum
--   - encoding: S supports g if the pointwise stabiliser Stab•(S) ≤ Γ_n fixes g (C rigid) → every automorphism extending an element of the pointwise stabiliser of S fixes g; reason: for a rigid circuit each element has exactly one extension, so the two agree; supports are only applied to reduced (hence rigid, Lemma 2.3) circuits or to rigidifications
--   - reading: sup(g): the unique minimal support, 'contained in every support of g' → sup(g) := intersection of all supports with fewer than n/2 points on each side; reason: containment in every support is false for large supports (n = 20, the reduced circuit summing all 400 variables: {L1,R1} and {L2,…,L20,R1} both support x_{1,1}); by [DPS26a, Lemmas 2.1, 2.2] the intersection of the small supports is the unique minimal small support, the only object the source's later arguments use
--   - encoding: depth: maximum number of wires on an input-to-output path → depth = that maximum, read as 0 when no input-to-output path exists; reason: the maximum of the empty set occurs only for circuits without input gates
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 29 (PDF p. 32), Theorem B.2

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Circuit
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Support
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Forestwidth

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Theorem B.2, printed p. 29 (PDF p. 32). Let `Δ ≥ 1`, `k ≥ 2`, `n ≥ 2k + 1`, and let `F` be a
bipartite multigraph with `fw_Δ(F) ≤ k − 1`. Then `hom_{F,n}` is computed by a reduced
matrix-symmetric circuit of support size `≤ k`, support depth `≤ Δ`, orbit size `≤ n^k`, depth
`≤ 2Δ + 1`, and size `≤ 5 n^k (|V(F)| + |E(F)|) + 1`. -/
theorem bounded_forestwidth_circuit {K : Type} [Field K] [CharZero K] (Δ k n : ℕ)
    (hΔ : 1 ≤ Δ) (hk : 2 ≤ k) (hn : 2 * k + 1 ≤ n) (F : Pattern)
    (hF : forestwidth Δ F.graph + 1 ≤ (k : ℕ∞)) :
    ∃ (V : Type) (_ : Fintype V) (C : Circuit K n V),
      C.WellFormed ∧ C.MatrixSymmetric ∧ C.Reduced ∧
      C.maxSup ≤ k ∧ C.rigidSupportDepth ≤ Δ ∧ C.maxOrb ≤ n ^ k ∧
      C.depth ≤ 2 * Δ + 1 ∧ C.size ≤ 5 * n ^ k * (F.numVertices + F.numEdges) + 1 ∧
      C.Computes (F.homPoly K n) := by sorry

end SymmetricDepthHierarchy.ConstantDepth
