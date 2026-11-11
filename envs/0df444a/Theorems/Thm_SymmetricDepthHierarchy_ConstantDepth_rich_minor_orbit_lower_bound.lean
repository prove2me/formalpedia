-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_rich_minor_orbit_lower_bound
-- name    : SymmetricDepthHierarchy.ConstantDepth.rich_minor_orbit_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:32.482984+00:00
-- url     : https://prove2.me/theorems/70318c28-5546-458b-acbf-847295b6baab
-- title:
--   Corollary B.23: support depth $\le\Delta$ for $\mathrm{hom}_{F,N}$ with a rich minor forces orbit size $\ge\binom{N}{k+1}$
-- statement:
--   Let $\Delta\ge1$ and $k\ge2$. Let $G$ be a connected $(\Delta,k)$-rich graph and $F$ a bipartite multigraph containing $G$ as a minor. Let
--   $$N\ge\max\{\gamma(G),\,4(k+1),\,20\}.$$
--   Then every matrix-symmetric circuit over $X_N$ of support depth $\le\Delta$ computing $\mathrm{hom}_{F,N}$ has orbit size at least $\binom{N}{k+1}$.
--
--   The support depth of an arbitrary circuit is that of its rigidification; no reducedness is assumed.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, variables x_{i,j} → Fin n (0-based), variables indexed by Fin n × Fin n; reason: relabelling of [n]; the same polynomials and circuits
--   - encoding: S supports g if the pointwise stabiliser Stab•(S) ≤ Γ_n fixes g (C rigid) → every automorphism extending an element of the pointwise stabiliser of S fixes g; reason: for a rigid circuit each element has exactly one extension, so the two agree; supports are only applied to reduced (hence rigid, Lemma 2.3) circuits or to rigidifications
--   - reading: sup(g): the unique minimal support, 'contained in every support of g' → sup(g) := intersection of all supports with fewer than n/2 points on each side; reason: containment in every support is false for large supports (n = 20, the reduced circuit summing all 400 variables: {L1,R1} and {L2,…,L20,R1} both support x_{1,1}); by [DPS26a, Lemmas 2.1, 2.2] the intersection of the small supports is the unique minimal small support, the only object the source's later arguments use
--   - reading: height of a gate: maximal number of wires on a path from it to an input gate (Appendix A); undefined for gates with no path to an input → height: length of a longest downward path (to any gate without children); reason: the two agree whenever every internal gate has a child; with the literal definition, childless internal gates (empty sums/products) have no height and the rigidification would be undefined or would merge gates computing 0 and 1
--   - encoding: γ(G) = ∑_v 2^{deg_G(v) − 1} → ∑_v 2^(deg_G(v) - 1) with natural-number subtraction; reason: every vertex of G has positive degree here (G connected with at least two vertices), so no truncation occurs
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 40 (PDF p. 43), Corollary B.23

import Mathlib
import Definitions.Def_HadwigerConj_Defs
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Circuit
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Support
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Rigidification
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Richness
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_CFI

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Corollary B.23, printed p. 40 (PDF p. 43). Let `Δ ≥ 1` and `k ≥ 2`. Let `G` be a connected
`(Δ, k)`-rich graph and `F` a bipartite multigraph containing `G` as a minor. Let
`N ≥ max {γ(G), 4(k + 1), 20}`. Then every matrix-symmetric circuit of support depth `≤ Δ`
computing `hom_{F,N}` has orbit size at least `binom(N, k + 1)`. -/
theorem rich_minor_orbit_lower_bound {K : Type} [Field K] [CharZero K] (Δ k : ℕ) (hΔ : 1 ≤ Δ)
    (hk : 2 ≤ k) (G : FinGraph) (hG : G.G.Connected) (hrich : Rich Δ k G.G) (F : Pattern)
    (hFG : HadwigerConj.IsMinor G.G F.graph) (N : ℕ) (hNγ : cfiSize G.G ≤ N)
    (hNk : 4 * (k + 1) ≤ N) (hN20 : 20 ≤ N) {V : Type} [Fintype V] (C : Circuit K N V)
    (hC : C.WellFormed) (hsym : C.MatrixSymmetric) (hsd : C.supportDepth ≤ Δ)
    (hcomp : C.Computes (F.homPoly K N)) : N.choose (k + 1) ≤ C.maxOrb := by sorry

end SymmetricDepthHierarchy.ConstantDepth
