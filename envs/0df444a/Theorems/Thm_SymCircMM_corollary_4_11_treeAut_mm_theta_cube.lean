-- Prove2me | Theorems.Thm_SymCircMM_corollary_4_11_treeAut_mm_theta_cube
-- name    : SymCircMM.corollary_4_11_treeAut_mm_theta_cube
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:41.157908+00:00
-- url     : https://prove2.me/theorems/96cd14d9-fce0-4bc9-b2c9-e10df1738f82
-- title:
--   Corollary 4.11 — over every field of characteristic $\ne2$, $C^{G_k}(\mathrm{MM}_n)=\Theta(n^3)$
-- statement:
--   Let $k\ge0$, $n=2^k$, and let $G_k=\mathrm{Aut}(T_k)$ act on the variables of $n\times n$ matrix multiplication by permuting the inner index (the columns of $A$ and the rows of $B$ simultaneously), the inner index set being the leaves $\{0,1\}^k$. Over every field $F$ with $\mathrm{char}(F)\ne2$,
--
--   $$C^{G_k}(\mathrm{MM}_n)=\Theta(n^3);$$
--
--   explicitly, uniformly in $F$ and $k$:
--
--   1. every $G_k$-symmetric algebraic circuit $C$ computing $\mathrm{MM}_n$ (any fan-in, size counted in edges) satisfies $n^3\le2\,\mathrm{size}(C)$;
--   2. some $G_k$-symmetric circuit computing $\mathrm{MM}_n$ has size at most $4n^3-2n^2$ (the divide-and-conquer circuit $D_k$).
--
--   The divide-and-conquer circuit is therefore optimal up to a constant factor among $G_k$-symmetric circuits, although $|G_k|=2^{n-1}$ is exponentially smaller than $|S_n|$.
--
--   **Formalization Note** The lower bound covers the relaxed notion of symmetry (repeated input labels, no output condition); the circuit of item 2 is symmetric in the paper's sense (one input gate per label, every extension fixing the output gates).
--
--   Differences from the source:
--
--   - encoding: [n] identified with the leaves {0,1}^k of T_k, and G_k = Aut(T_k) acting faithfully on the leaves → Leaf k = Fin k → Bool and treeAut k, the permutations of the leaves that preserve, for every depth i ≤ k, the relation "below the same node of depth i"; reason: these are exactly the leaf permutations induced by automorphisms of T_k (which permute the leaf sets L(v), PDF p.7), and the induced action is faithful
--   - encoding: an algebraic circuit (a finite labelled multi-DAG with designated output gates) and the polynomial ĝ ∈ F[X] of each gate → Circuit F X γ on a finite gate type γ (labels, edge multiplicities wire g c, a rank function for acyclicity); gate values in MvPolynomial X F; the output gates given by a map out : ι × ι → γ; reason: the same objects; "computing MM_n" is equality of polynomials at the designated output gates
--   - generalization: a G-symmetric circuit (Definition 2.2): one input gate per variable, and σ̂ permutes (by Remark 2.4, fixes) the output gates → IsGSymmetric: for each σ ∈ G some bijection of the gates preserving edge multiplicities and labels, variables renamed by (2); input labels may repeat and nothing is required of the output gates; reason: every circuit symmetric in the paper's sense is symmetric in this sense, so the lower bound covers more circuits; the proof passes to the rigidified circuit of Proposition 4.2, where the extension is unique, and never uses the output condition
--   - encoding: a G-symmetric circuit computing MM_n (Definition 2.2 with the requirement σ̂ · g_r = g_r of Remark 2.4) → IsGSymmetricStrict G out: each label on at most one input gate, and every σ ∈ G extends to an automorphism fixing every output gate out (a, b); reason: the paper's notion for the individually invariant entries of MM_n, used for the circuit whose existence is asserted
--   - generalization: C^G(MM_n) = Θ(n³) → every G-symmetric circuit computing MM_n has n³ ≤ 2·size, and some G-symmetric circuit computing MM_n has size ≤ 4n³ − 2n²; reason: explicit constants, uniform in n, F and G, imply Θ(n³); both are the paper's (D_k, PDF p.8, and n³/2 from Theorem 3.5, PDF p.14)
--   - encoding: char(F) ≠ 2 → ringChar F ≠ 2; reason: the same condition
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Corollary 4.11, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_SymCircMM_Circuit_IsGSymmetric
import Definitions.Def_SymCircMM_treeAut

set_option autoImplicit false

namespace SymCircMM

/-- **Corollary 4.11** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.14 (PDF p.15)): "Over any field F with char(F) ≠ 2,
C^{G_k}(MM_n) = Θ(n³)." Here `n = 2^k` and `G_k = Aut(T_k)` acts on the inner index by (2).

**Formalization Note.** `Θ(n³)` is stated with the paper's explicit constants, uniformly in `F` and
`k`: (1) every `G_k`-symmetric circuit computing `MM_n` (any finite gate set, unbounded fan-in, size =
edges with multiplicity) has `n³ ≤ 2 · size` ("`C^G(MM_n) ≥ n³/2`", proof of Corollary 4.9, p.13
(PDF p.14)); (2) some `G_k`-symmetric circuit computing `MM_n` has size at most `4n³ − 2n²` (the
divide-and-conquer circuit `D_k`, p.7 (PDF p.8)). The lower bound covers every circuit symmetric in
the relaxed sense `IsGSymmetric` (no output condition, repeated input labels allowed); the upper bound
is a circuit symmetric in the paper's sense (`IsGSymmetricStrict`). `char F ≠ 2` is
`ringChar F ≠ 2`. -/
theorem corollary_4_11_treeAut_mm_theta_cube (F : Type) [Field F] (hF : ringChar F ≠ 2) (k : ℕ) :
    (∀ {γ : Type} [Fintype γ] (C : Circuit F (MMVar (Leaf k)) γ),
        C.IsGSymmetric (treeAut k) → C.ComputesMM → (2 ^ k) ^ 3 ≤ 2 * C.size) ∧
    (∃ (γ : Type) (_ : Fintype γ) (C : Circuit F (MMVar (Leaf k)) γ) (out : Leaf k × Leaf k → γ),
        C.IsGSymmetricStrict (treeAut k) out ∧ C.ComputesMMAt out ∧
        C.size ≤ 4 * (2 ^ k) ^ 3 - 2 * (2 ^ k) ^ 2) := by sorry

end SymCircMM
