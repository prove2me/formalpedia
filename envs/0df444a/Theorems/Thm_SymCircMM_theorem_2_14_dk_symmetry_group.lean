-- Prove2me | Theorems.Thm_SymCircMM_theorem_2_14_dk_symmetry_group
-- name    : SymCircMM.theorem_2_14_dk_symmetry_group
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:41.215462+00:00
-- url     : https://prove2.me/theorems/ddf318ba-c6b9-4838-93e2-bf35103d4cf0
-- title:
--   Theorem 2.14 — the symmetry group of $D_k$ is exactly $G_k$; $D_k$ has size $4n^3-2n^2$
-- statement:
--   Let $n=2^k$ and let $\sigma\in S_n$ act on the variables by (2). Then:
--
--   1. the map $A_{ij}\mapsto A_{i,\sigma(j)}$, $B_{j\ell}\mapsto B_{\sigma(j),\ell}$ on the input gates of $D_k$ extends to an automorphism of $D_k$ if and only if $\sigma\in G_k$;
--   2. the output gates $g^\varepsilon_{i\ell}$ of $D_k$ compute $\mathrm{MM}_n$;
--   3. $D_k$ has size $4n^3-2n^2=O(n^3)$;
--   4. $G_k$ is the largest subgroup $G\le S_n$ such that $D_k$ is $G$-symmetric: $D_k$ is $G$-symmetric if and only if $G\le G_k$;
--   5. for $\sigma\in G_k$ every extension fixes every output gate;
--   6. hence $D_k$ is $G_k$-symmetric with output gates $g^\varepsilon_{i\ell}$ in the sense of Definition 2.2.
--
--   This is the upper bound of the goal and the reason for studying $G_k$: any circuit for $\mathrm{MM}_n$ of size $o(n^3)$ must break the symmetry of the recursive block decomposition.
--
--   Differences from the source:
--
--   - encoding: [n] identified with the leaves {0,1}^k of T_k, and G_k = Aut(T_k) acting faithfully on the leaves → Leaf k = Fin k → Bool and treeAut k, the permutations of the leaves that preserve, for every depth i ≤ k, the relation "below the same node of depth i"; reason: these are exactly the leaf permutations induced by automorphisms of T_k (which permute the leaf sets L(v), PDF p.7), and the induced action is faithful
--   - encoding: an algebraic circuit (a finite labelled multi-DAG with designated output gates) and the polynomial ĝ ∈ F[X] of each gate → Circuit F X γ on a finite gate type γ (labels, edge multiplicities wire g c, a rank function for acyclicity); gate values in MvPolynomial X F; the output gates given by a map out : ι × ι → γ; reason: the same objects; "computing MM_n" is equality of polynomials at the designated output gates
--   - generalization: D_k is a G_k-symmetric circuit of size O(n³) → size (dk F k) = 4 · (2^k)³ − 2 · (2^k)²; reason: the exact count n³ · 2 + n²(n − 1) · 2 stated on PDF p.8, which implies O(n³)
--   - encoding: G_k is the largest subgroup G ≤ S_n such that D_k is G-symmetric → ∀ G, (dk F k).IsGSymmetric G ↔ G ≤ treeAut k; reason: for D_k, with one input gate per variable, the relaxed and the strict notions agree by item 5; the iff says exactly "largest"
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Theorem 2.14, p.7 (PDF p.8); proof Appendix A, pp.15–16 (PDF pp.16–17); size count, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_SymCircMM_dk
import Definitions.Def_SymCircMM_Circuit_IsGSymmetric

set_option autoImplicit false

namespace SymCircMM

/-- **Theorem 2.14** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.7 (PDF p.8); proof Appendix A, pp.15–16 (PDF pp.16–17)): "Let σ ∈ S_n act on
X by (2). The map A_{ij} ↦ A_{i,σ(j)}, B_{jℓ} ↦ B_{σ(j),ℓ} on the input gates of D_k extends to an
automorphism of D_k if and only if σ ∈ G_k. Consequently, D_k is a G_k-symmetric circuit of size O(n³)
computing MM_n, and G_k is the largest subgroup G ≤ S_n such that D_k is G-symmetric. Moreover, for
σ ∈ G_k the extension fixes every output gate."

**Formalization Note.** `n = 2^k`, leaves `{0,1}^k`. The conjuncts: (1) the extension criterion;
(2) the output gates `g^ε_{iℓ}` compute `MM_n`; (3) the exact size `4n³ − 2n²` (p.7 (PDF p.8)), which
gives `O(n³)`; (4) `D_k` is `G`-symmetric exactly for the subgroups `G ≤ G_k`; (5) every extension of
`σ ∈ G_k` fixes every output gate; (6) hence `D_k` is `G_k`-symmetric with outputs `g^ε_{iℓ}` in the
paper's sense (one input gate per variable, extensions fixing the outputs). The circuit has no
constants, so the field is arbitrary. -/
theorem theorem_2_14_dk_symmetry_group (F : Type) [Field F] (k : ℕ) :
    (∀ σ : Equiv.Perm (Leaf k), (∃ φ, (dk F k).Extends (mmAct σ) φ) ↔ σ ∈ treeAut k) ∧
    (dk F k).ComputesMMAt (dkOut k) ∧
    (dk F k).size = 4 * (2 ^ k) ^ 3 - 2 * (2 ^ k) ^ 2 ∧
    (∀ G : Subgroup (Equiv.Perm (Leaf k)), (dk F k).IsGSymmetric G ↔ G ≤ treeAut k) ∧
    (∀ σ ∈ treeAut k, ∀ φ, (dk F k).Extends (mmAct σ) φ →
        ∀ a b, φ (dkOut k (a, b)) = dkOut k (a, b)) ∧
    (dk F k).IsGSymmetricStrict (treeAut k) (dkOut k) := by sorry

end SymCircMM
