-- Prove2me | Theorems.Thm_SubspaceConv_Supplement_theorem_3
-- name    : SubspaceConv.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:50:05.490064+00:00
-- url     : https://prove2.me/theorems/3f3ae7d2-d362-427c-83cb-ef149f2897fd
-- title:
--   Theorem 3 — Grassmann-graph kernel product in $O_q(N\log N)$ operations (corrected: $C(N\log N+1)$ at $N=1$)
-- statement:
--   Let $\mathbb F_q$ have characteristic $p$, let $R$ be a commutative ring in which $p$ is invertible, and let $k \le n$. Put $V = \mathrm{Gr}_q(n,k)$, $N = |V|$, $d = \min(k, n-k)$, and $\mathrm{dist}(U,W) = k - \dim(U \cap W)$. Given $a_0, \dots, a_d \in R$ and $f : V \to R$, the product
--
--   $$(Kf)(U) = \sum_{W \in V} a_{\mathrm{dist}(U,W)}\, f(W), \qquad U \in V,$$
--
--   can be computed in $O_q(N \log N)$ arithmetic operations in $R$, by one program that takes $a_0, \dots, a_d$ and $f$ as inputs.
--
--   This gives fast matrix–vector products for every matrix invariant under $\mathrm{GL}(n,q)$ on the Grassmann graph $J_q(n,k)$, including its distance matrices and adjacency matrix.
--
--   **Formalization Note** The model is the arithmetic straight-line program `SubspaceConv.Supplement.ArithSLP` (the published linear model plus the free constant $1$ and a multiplication gate), evaluated over every commutative ring with $p \cdot p^{-1} = 1$. The bound is $C\,(N \log N + 1)$ with one constant $C$ depending only on the field, for every $k \le n$.
--
--   Differences from the source:
--   - correction: O_q(N log N) operations → at most C·(N·log N + 1) operations; reason: at k = 0 (or k = n) N = 1, so N log N = 0, but (Kf)(V) = a_0·f(V) needs one multiplication of two inputs; the paper's proof (p.15) says these cases take O(1) operations
--   - encoding: under the coefficient assumption of theorem 1, O_q(·) arithmetic operations → one well-formed ring-uniform program evaluated over every commutative ring A with p·pinv = 1; one real constant C chosen after F only; reason: the published convention of SubspaceConv.theorem_1; same instances
--   - encoding: a_0, …, a_d indexed by distance → a : Fin (d+1) → A, read at the distance (a fallback 0 is never reached); reason: dist(U,W) ≤ d always; same instances
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), Theorem 3, p.3 (PDF p.4); proof §5.3, p.15–16

import Mathlib
import Definitions.Def_SubspaceConv_Supplement_Gr
import Definitions.Def_SubspaceConv_Supplement_ArithSLP
import Definitions.Def_SubspaceConv_Supplement_kernelMul

set_option autoImplicit false

universe u

namespace SubspaceConv.Supplement

/-- **Theorem 3** (Fast multiplication on the Grassmann graph), Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), p.3 (PDF p.4). Let
`V = Gr_q(n, k)`, `N = |V|` and `d = min(k, n − k)`. Under the coefficient assumption of
theorem 1, given `a_0, …, a_d ∈ R` and `f : V → R`, the product `Kf`,
`(Kf)(U) = ∑_{W ∈ V} a_{dist(U,W)} f(W)`, can be computed in `O_q(N log N)` arithmetic operations
in `R`.

**Formalization Note** The model is the arithmetic straight-line program
`SubspaceConv.Supplement.ArithSLP` (published `LinSLP` plus a free constant `one` and a
multiplication gate `mul`, each `add`, `sub`, `mul`, `zmul`, `invp` costing one). For each `(F, n, k)`
with `k ≤ n` there is one well-formed program whose inputs are the coefficients and the weights
(`Fin (d + 1) ⊕ V`), whose outputs are indexed by `V`, and which computes `Kf` over every
commutative ring `A` with `p · pinv = 1`. One real constant `C` depends only on `F`. The bound is
`C · (N log N + 1)` (natural logarithm): at `k = 0` or `k = n`, `N = 1` and `N log N = 0`, while
`a_0 f(V)` needs one multiplication (the paper, p.15: "The cases k = 0, n have one entry and take
O(1) operations"). -/
theorem theorem_3 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℝ, ∀ n k : ℕ, k ≤ n →
      ∃ P : ArithSLP (Fin (min k (n - k) + 1) ⊕ Gr F n k) (Gr F n k),
        P.WellFormed ∧
        (P.cost : ℝ) ≤ C * ((Fintype.card (Gr F n k) : ℝ) *
          Real.log (Fintype.card (Gr F n k) : ℝ) + 1) ∧
        ∀ (A : Type u) [CommRing A] (pinv : A), (ringChar F : A) * pinv = 1 →
          ∀ (a : Fin (min k (n - k) + 1) → A) (f : Gr F n k → A),
            P.eval pinv (Sum.elim a f) = kernelMul a f := by sorry

end SubspaceConv.Supplement
