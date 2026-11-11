-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_sparse_lifting
-- name    : SparseHamiltonianNorm.Simulation.sparse_lifting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:42.070977+00:00
-- url     : https://prove2.me/theorems/156ed236-d506-43f5-804b-47933cf03fbf
-- title:
--   Lemma 6 — Sparse-entry lifting and compressed second moment
-- statement:
--   Let $1\le d\le N$, $\Lambda>0$, and $0<\Lambda_{\max}\le\Lambda$. Let $H$ satisfy the Hermitian sparse and norm promises, and let $f$ be any row permutations listing its support. For the explicit operators $V,M$ of Eqs. (25)–(26),
--   $$V^\dagger V=I,\quad M=M^\dagger,\quad H=2\sqrt d\,\Lambda V^\dagger MV,\quad V^\dagger M^2V\preceq I/4,$$
--   $$\|M\|_{\mathrm{op}}=\frac{\sqrt d}{2\Lambda}\max_{i,j}|H_{ij}|\le\frac{\sqrt d\Lambda_{\max}}{2\Lambda}\le\frac{\sqrt d}{2}.$$
--   The identities and bounds connect the original sparse access model with the compressed-moment setting; no spectral-norm bound on $H$ is imposed.
--
--   Differences from the source:
--   - encoding: one-based address indices and the isometry/Hermitian operators defined before Lemma 6 → zero-based Fin indices and explicit isometry and Hermiticity conjuncts; reason: the extra conjuncts expose properties of the source-defined operators without changing the input hypotheses
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Lemma 6, p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf#page=12; printed page = PDF page; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_SparseLift

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SparseHamiltonianNorm.Simulation
/-- Li--Wang, Lemma 6, p.12, Eqs. (27)--(28). -/
theorem sparse_lifting (N d : ℕ) (Λ Λmax : ℝ)
    (hD : 1 ≤ d) (hDN : d ≤ N) (hΛ : 0 < Λ) (hmax : 0 < Λmax) (hmaxΛ : Λmax ≤ Λ)
    (H : Matrix (Fin N) (Fin N) ℂ) (f : Fin N → Equiv.Perm (Fin N))
    (hH : SparsePromise d Λ Λmax H) (hf : ListsSupport d H f) :
    let V := sparseV N d
    let M := sparseM d Λ H f
    V.conjTranspose * V = 1 ∧ M.IsHermitian ∧
    H = compressedH d Λ V M ∧ CompressedMoment V M ∧
    opNorm M = Real.sqrt d / (2 * Λ) * entryNorm H ∧
    opNorm M ≤ Real.sqrt d * Λmax / (2 * Λ) ∧
    Real.sqrt d * Λmax / (2 * Λ) ≤ Real.sqrt d / 2 := by sorry
end SparseHamiltonianNorm.Simulation
