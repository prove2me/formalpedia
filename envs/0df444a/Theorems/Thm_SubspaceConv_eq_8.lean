-- Prove2me | Theorems.Thm_SubspaceConv_eq_8
-- name    : SubspaceConv.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:03.357879+00:00
-- url     : https://prove2.me/theorems/7e8b75f4-fc07-447f-a509-a1e7f66954bf
-- title:
--   Eq. (8) — $g_0=Z_{n-1,k}f_0$ and $(g_1)_D(x+D)=g_0(D)+(\mathsf Af_1)_D(x+D)$
-- statement:
--   Let $g=Z_{n+1,k}f$ for a table $f$ on the subspaces of $\mathbb F_q^{n+1}$ of dimension at most $k$, with values in a commutative coefficient ring. Split the input into
--   $$f_0(B)=f(B\times\{0\})\ (\dim B\le k),\qquad (f_1)_B(x+B)=f\big(U(B,x+B)\big)\ (\dim B\le k-1),$$
--   and index the output parts $g_0,g_1$ in the same way. Then
--   $$g_0=Z_{n,k}f_0,\qquad (g_1)_D(x+D)=g_0(D)+(\mathsf Af_1)_D(x+D),$$
--   where $\mathsf A$ is the coset operator of §3.1 with directions of dimension at most $k-1$.
--
--   With cutoff $k$, inside subspaces have dimension at most $k$, and crossing subspaces have directions of dimension at most $k-1$. This is the block form of $Z_{n,k}$ under the hyperplane cut; it reduces the transform to one inside transform and the coset operator $\mathsf A$.
--
--   **Formalization Note** The paper's $n$ is $n+1$ here. The split tables are given with their defining equations, and $g_0(D)$, $(g_1)_D(x+D)$ are the values of $g$ at any table index equal to $D\times\{0\}$, resp. $U(D,x+D)$. At $k=0$ there is no crossing subspace of dimension $\le0$, so the second identity is empty, as is the paper's table for the negative cutoff.
--
--   Differences from the source:
--   - encoding: ambient F_q^n, inside part on F_q^{n−1} → ambient Fin (n+1) → F, inside part on Fin n → F; reason: avoids natural-number subtraction
--   - generalization: tables with values in ℂ (§3 works over ℂ until §3.4) → values in any additive commutative monoid; reason: the identity is pure summation; ℂ and every commutative ring are instances
--   - encoding: f₀, f₁, g₀, g₁ defined by restriction to inside and crossing subspaces → f₀, f₁ given with their defining equations as hypotheses; g₀(D), (g₁)_D(x + D) read as g(W) for W = D × {0}, resp. W = U(D, x + D); reason: avoids membership proofs inside the statement; every index of f₀, f₁ has such a W, so the tables are determined
--   - encoding: directions of dimension at most k − 1, empty for k = 0 → directions in the type of subspaces of dimension at most k − 1 (natural-number subtraction), with no crossing W of dimension ≤ 0 at k = 0; reason: at k = 0 both clauses about crossing outputs are vacuous, as the paper's empty table
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.1, eq. (8), p.12 (PDF p.13)

import Mathlib
import Definitions.Def_SubspaceConv_SubLE
import Definitions.Def_SubspaceConv_zeta
import Definitions.Def_SubspaceConv_crossSub
import Definitions.Def_SubspaceConv_cosetSum

namespace SubspaceConv

/-- **Eq. (8)**, Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.1, p.12 (PDF p.13). Let `g = Z_{n+1,k} f` for a table `f` on the
subspaces of `F^{n+1}` of dimension at most `k`. Split the input into
`f_0(B) = f(B × {0})` (`dim B ≤ k`) and `(f_1)_B(x + B) = f(U(B, x + B))` (`dim B ≤ k − 1`), and
the output likewise. Then `g_0 = Z_{n,k} f_0` and `(g_1)_D(x + D) = g_0(D) + (A f_1)_D(x + D)`.

**Formalization Note** The paper's `n` is `n + 1` here. The split tables are given with the
equations defining them (`hf₀`, `hf₁`), and the outputs `g_0(D)`, `(g_1)_D(x + D)` are the values
of `g` at any `W` equal to `D × {0}`, resp. `U(D, x + D)`; this avoids membership proofs inside
the statement. For `k = 0` there are no crossing subspaces of dimension `≤ 0`, so the second
clause is empty, as the paper's empty table for the negative cutoff `k − 1`. Values lie in any
additive commutative monoid (the identity is pure summation). -/
theorem eq_8 (F : Type) [Field F] [Fintype F] [DecidableEq F] (n k : ℕ)
    {A : Type*} [AddCommMonoid A] (f : SubLE F (n+1) k → A)
    (f₀ : SubLE F n k → A)
    (hf₀ : ∀ (B : SubLE F n k) (U : SubLE F (n+1) k), U.1 = insideSub B.1 → f₀ B = f U)
    (f₁ : (B : SubLE F n (k - 1)) → (Fin n → F) ⧸ B.1 → A)
    (hf₁ : ∀ (B : SubLE F n (k - 1)) (x : Fin n → F) (U : SubLE F (n+1) k),
      U.1 = crossSub B.1 x → f₁ B (Submodule.Quotient.mk x) = f U) :
    (∀ (D : SubLE F n k) (W : SubLE F (n+1) k), W.1 = insideSub D.1 → zeta f W = zeta f₀ D) ∧
    (∀ (D : SubLE F n (k - 1)) (D' : SubLE F n k) (x : Fin n → F) (W : SubLE F (n+1) k),
      D'.1 = D.1 → W.1 = crossSub D.1 x →
        zeta f W = zeta f₀ D' + cosetSum f₁ D (Submodule.Quotient.mk x)) := by sorry

end SubspaceConv
