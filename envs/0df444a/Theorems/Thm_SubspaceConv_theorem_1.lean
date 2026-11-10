-- Prove2me | Theorems.Thm_SubspaceConv_theorem_1
-- name    : SubspaceConv.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:17.795764+00:00
-- url     : https://prove2.me/theorems/d425b5e9-f215-4f36-a76c-6460008f8542
-- title:
--   Theorem 1 — $Z_{n,k}$, $Z_{n,k}^{-1}$, $Z_{n,k}^{\mathsf T}$, $(Z_{n,k}^{\mathsf T})^{-1}$ in $O_q(nk\,M_q(n,k))=O_q(M_q(n,k)\log M_q(n,k))$ operations
-- statement:
--   **Theorem 1 (Fast Subspace Summation).** Let $\mathbb F_q$ be a finite field of characteristic $p$. Over any commutative ring in which $p$ is invertible, each of
--   $$Z_{n,k},\qquad Z_{n,k}^{-1},\qquad Z_{n,k}^{\mathsf T},\qquad (Z_{n,k}^{\mathsf T})^{-1}$$
--   can be applied in $O_q(nk\,M_q(n,k))$ arithmetic operations for $k\le n$. In particular, the cost is $O_q(M_q(n,k)\log M_q(n,k))$.
--
--   Here $Z_{n,k}$ is the truncated subspace zeta transform $(Z_{n,k}f)(W)=\sum_{U\le W,\ \dim U\le k}f(U)$ on tables indexed by the $M_q(n,k)$ subspaces of $\mathbb F_q^n$ of dimension at most $k$, and $Z_{n,k}^{\mathsf T}$ sums over superspaces.
--
--   Precisely: there are constants $C$ and $C'$, depending only on $\mathbb F_q$, such that for all $k\le n$ there are four linear straight-line programs, each with at most
--   $$C\,n\,k\,M_q(n,k)\quad\text{and at most}\quad C'\,M_q(n,k)\,\log M_q(n,k)$$
--   operations (additions, subtractions, multiplications by integers and by $p^{-1}$), which compute $Z_{n,k}f$, $Z_{n,k}^{-1}f$, $Z_{n,k}^{\mathsf T}f$ and $(Z_{n,k}^{\mathsf T})^{-1}f$ for every table $f$ over every commutative ring $A$ with an element $p^{-1}$, $p\cdot p^{-1}=1$.
--
--   The covering-pair algorithms take $\Theta_q(N_q(n)q^{n/2})$ operations at $k=n$, and Kennes proved a matching lower bound for addition-only algorithms; Theorem 1 reaches $O_q(N_q(n)\log N_q(n))$ by using subtraction and scaling.
--
--   **Formalization Note** One program per $(n,k)$ is evaluated over every such ring (it is ring-uniform). A program $P$ for an inverse is specified by both $Z(Pf)=f$ and $P(Zf)=f$ for every table $f$. The logarithm is natural; at $M_q(n,k)=1$ (that is, $k=0$) both bounds are $0$, attained by a program that only reads its input.
--
--   Differences from the source:
--   - generalization: "Over any commutative ring in which p is invertible, … can be applied in O_q(nkM_q(n,k)) arithmetic operations" (for each ring, some algorithm counting ring additions, subtractions and multiplications) → for each (n, k) one well-formed linear straight-line program, evaluated over every commutative ring A with p · pinv = 1, whose operations are additions, subtractions, integer scalings and multiplications by p⁻¹, each counted; reason: the paper's circuit is linear (§3.3, gates z = x + y, z = cx) with integer constants and divisions only by powers of p (§3.4); a single program valid over every such ring is in particular an algorithm for each ring, so the Lean statement specializes to the printed one
--   - encoding: O_q(·), "Constants in O_q(·) depend only on q" → explicit constants C ∈ ℕ and C′ ∈ ℝ depending only on F, chosen before n and k; reason: the meaning of O_q fixed on p.11
--   - encoding: a ring in which p is invertible → a commutative ring A with an element pinv, p · pinv = 1; reason: the inverse of p is unique
--   - encoding: Z⁻¹_{n,k}, (Z^T_{n,k})⁻¹ → programs P with Z(Pf) = f and P(Zf) = f (resp. with Z^T) for every table f; reason: Z_{n,k} is unitriangular, hence invertible over every ring, and either equation pins Pf = Z⁻¹f
--   - encoding: the M_q(n,k) × M_q(n,k) matrices, rows and columns ordered by dimension → tables indexed by the type of subspaces of F^n of dimension at most k; reason: relabelling entries costs nothing; no enumeration of subspaces is part of the statement
--   - encoding: log M_q(n,k) → natural logarithm Real.log; reason: a change of base is a constant factor, absorbed in C′
--   - encoding: every finite field F_q → every finite field F in the universe Type, with a DecidableEq instance; reason: every finite field is isomorphic to one in Type (e.g. a Galois field), the statement is invariant under field isomorphism, and DecidableEq holds classically
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), Theorem 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_SubspaceConv_LinSLP
import Definitions.Def_SubspaceConv_SubLE
import Definitions.Def_SubspaceConv_Mq
import Definitions.Def_SubspaceConv_zeta
import Definitions.Def_SubspaceConv_zetaT

universe u

namespace SubspaceConv

/-- **Theorem 1** (Fast Subspace Summation), Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), p.2 (PDF p.3). Over any commutative ring in
which `p` is invertible, each of `Z_{n,k}`, `Z_{n,k}^{−1}`, `Z_{n,k}^T` and `(Z_{n,k}^T)^{−1}` can be
applied in `O_q(nk M_q(n, k))` arithmetic operations for `k ≤ n`. In particular, the cost is
`O_q(M_q(n, k) log M_q(n, k))`.

**Formalization Note** There are constants `C ∈ ℕ` and `C' ∈ ℝ`, depending only on the field `F`
(chosen before `n` and `k`), such that for all `k ≤ n` there are four well-formed ring-uniform
linear straight-line programs (`SubspaceConv.LinSLP`: free input reads and zero, every addition,
subtraction, integer scaling and multiplication by `p⁻¹` costs one operation), each with inputs
and outputs indexed by the subspaces of `F^n` of dimension at most `k`, each of cost at most
`C · n · k · M_q(n, k)` and at most `C' · M_q(n, k) · log M_q(n, k)` (natural logarithm), which
compute `Z_{n,k}`, `Z_{n,k}^{−1}`, `Z_{n,k}^T` and `(Z_{n,k}^T)^{−1}` over every commutative ring `A`
with an element `pinv`, `p · pinv = 1`. A program `P` for an inverse is specified by both
composition equations, `Z (P f) = f` and `P (Z f) = f` for every table `f`. -/
theorem theorem_1 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℕ, ∃ C' : ℝ, ∀ n k : ℕ, k ≤ n →
      ∃ P₁ P₂ P₃ P₄ : LinSLP (SubLE F n k) (SubLE F n k),
        (P₁.WellFormed ∧ P₂.WellFormed ∧ P₃.WellFormed ∧ P₄.WellFormed) ∧
        (P₁.cost ≤ C * n * k * Mq F n k ∧ P₂.cost ≤ C * n * k * Mq F n k ∧
          P₃.cost ≤ C * n * k * Mq F n k ∧ P₄.cost ≤ C * n * k * Mq F n k) ∧
        ((P₁.cost : ℝ) ≤ C' * (Mq F n k : ℝ) * Real.log (Mq F n k) ∧
          (P₂.cost : ℝ) ≤ C' * (Mq F n k : ℝ) * Real.log (Mq F n k) ∧
          (P₃.cost : ℝ) ≤ C' * (Mq F n k : ℝ) * Real.log (Mq F n k) ∧
          (P₄.cost : ℝ) ≤ C' * (Mq F n k : ℝ) * Real.log (Mq F n k)) ∧
        ∀ (A : Type u) [CommRing A] (pinv : A), (ringChar F : A) * pinv = 1 →
          ∀ f : SubLE F n k → A,
            P₁.eval pinv f = zeta f ∧
            (zeta (P₂.eval pinv f) = f ∧ P₂.eval pinv (zeta f) = f) ∧
            P₃.eval pinv f = zetaT f ∧
            (zetaT (P₄.eval pinv f) = f ∧ P₄.eval pinv (zetaT f) = f) := by sorry

end SubspaceConv
