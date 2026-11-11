-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_forestwidth_characterisation
-- name    : SymmetricDepthHierarchy.ConstantDepth.forestwidth_characterisation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:31.757332+00:00
-- url     : https://prove2.me/theorems/50f8adbf-5011-4656-ba52-61f0c26e74d1
-- title:
--   Theorem 3.5: support size $\le k$ and support depth $\le\Delta$ iff a linear combination of $\mathrm{hom}_{F,n}$ with $\mathrm{fw}_\Delta(F)\le k-1$
-- statement:
--   Let $\Delta\ge1$, $k\ge2$ and $n\ge2k+1$. For a polynomial $p\in K[X_n]$ the following are equivalent:
--
--   1. $p$ is computed by a reduced matrix-symmetric circuit of support size $\le k$ and support depth $\le\Delta$;
--   2. $p$ is a linear combination of homomorphism polynomials $\mathrm{hom}_{F,n}$ for patterns $F$ with $\mathrm{fw}_\Delta(F)\le k-1$, i.e.
--   $$p\in\operatorname{span}_K\{\mathrm{hom}_{F,n}:\ \mathrm{fw}_\Delta(F)\le k-1\}.$$
--
--   This exact characterisation translates circuit lower bounds into statements about spans of homomorphism polynomials.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, variables x_{i,j} → Fin n (0-based), variables indexed by Fin n × Fin n; reason: relabelling of [n]; the same polynomials and circuits
--   - encoding: fw_Δ(F) ≤ k − 1 (least k ≥ 0 with a decomposition) → forestwidth Δ F.graph + 1 ≤ k in ℕ∞ (fw = ⊤ if no decomposition exists); reason: avoids truncated subtraction; for Δ ≥ 1 every finite graph has a decomposition, so fw is the source's finite minimum
--   - encoding: S supports g if the pointwise stabiliser Stab•(S) ≤ Γ_n fixes g (C rigid) → every automorphism extending an element of the pointwise stabiliser of S fixes g; reason: for a rigid circuit each element has exactly one extension, so the two agree; supports are only applied to reduced (hence rigid, Lemma 2.3) circuits or to rigidifications
--   - reading: sup(g): the unique minimal support, 'contained in every support of g' → sup(g) := intersection of all supports with fewer than n/2 points on each side; reason: containment in every support is false for large supports (n = 20, the reduced circuit summing all 400 variables: {L1,R1} and {L2,…,L20,R1} both support x_{1,1}); by [DPS26a, Lemmas 2.1, 2.2] the intersection of the small supports is the unique minimal small support, the only object the source's later arguments use
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 10 (PDF p. 13), Theorem 3.5; proofs in §B.1–§B.2, pp. 28–33 (PDF pp. 31–36)

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Circuit
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Support
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Forestwidth

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Theorem 3.5, printed p. 10 (PDF p. 13). Let `Δ ≥ 1`, `k ≥ 2`, `n ≥ 2k + 1`. For a polynomial
`p ∈ K[X_n]` the following are equivalent:
1. `p` is computed by a reduced matrix-symmetric circuit of support size `≤ k` and support depth
   `≤ Δ`;
2. `p` is a linear combination of homomorphism polynomials `hom_{F,n}` for patterns `F` with
   `fw_Δ(F) ≤ k − 1`. -/
theorem forestwidth_characterisation {K : Type} [Field K] [CharZero K] (Δ k n : ℕ)
    (hΔ : 1 ≤ Δ) (hk : 2 ≤ k) (hn : 2 * k + 1 ≤ n) (p : MvPolynomial (Fin n × Fin n) K) :
    (∃ (V : Type) (_ : Fintype V) (C : Circuit K n V),
        C.WellFormed ∧ C.MatrixSymmetric ∧ C.Reduced ∧
        C.maxSup ≤ k ∧ C.rigidSupportDepth ≤ Δ ∧ C.Computes p) ↔
      p ∈ Submodule.span K
        {q | ∃ F : Pattern, forestwidth Δ F.graph + 1 ≤ (k : ℕ∞) ∧ q = F.homPoly K n} := by sorry

end SymmetricDepthHierarchy.ConstantDepth
