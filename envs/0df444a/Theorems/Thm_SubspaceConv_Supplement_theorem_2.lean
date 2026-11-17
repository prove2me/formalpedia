-- Prove2me | Theorems.Thm_SubspaceConv_Supplement_theorem_2
-- name    : SubspaceConv.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:49:30.008243+00:00
-- url     : https://prove2.me/theorems/4a2f2a68-fc80-4037-a698-0f5f2cd1bab1
-- title:
--   Theorem 2 — $I_n^{a,b}$ and its transpose in $O_q(S\log S)$ operations
-- statement:
--   Let $\mathbb F_q$ be a finite field of characteristic $p$, and let $R$ be any commutative ring in which $p$ is invertible. For $0 \le a \le b \le n$ let $I_n^{a,b}$ be the incidence transform, $(I_n^{a,b}f)(W) = \sum_{U \le W,\, \dim U = a} f(U)$ for $W \in \mathrm{Gr}_q(n,b)$, and put
--
--   $$S = |\mathrm{Gr}_q(n,a)| + |\mathrm{Gr}_q(n,b)|,$$
--
--   the total input and output length. Then $I_n^{a,b}$ and its transpose can each be applied in
--
--   $$O_q(S \log S)$$
--
--   arithmetic operations, with a constant depending only on $q$.
--
--   The transform replaces the full subspace table (of size $q^{\Theta(n^2)}$) by tables of size $q^{O(n)}$ for low-rank summation, such as summing weights of projective points over every hyperplane; Theorem 7 shows the bound is optimal for $(n,a,b) = (4r, r, 3r)$ in the bounded-coefficient model.
--
--   **Formalization Note** The model is the published linear straight-line program `SubspaceConv.LinSLP` (free input reads and zero; additions, subtractions, integer scalings and multiplications by $p^{-1}$ cost one each). One constant $C$, depending only on the field, bounds both programs for every $0 \le a \le b \le n$, boundary cases included; $\log$ is natural, and $S \ge 2$. Each program is one ring-uniform program valid over every commutative ring with $p \cdot p^{-1} = 1$.
--
--   Differences from the source:
--   - encoding: under the coefficient assumption of theorem 1, O_q(·) arithmetic operations → one well-formed ring-uniform program evaluated over every commutative ring A with p·pinv = 1; one real constant C chosen after F only; reason: the published convention of SubspaceConv.theorem_1; same instances
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), Theorem 2, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_SubspaceConv_LinSLP
import Definitions.Def_SubspaceConv_Supplement_Gr
import Definitions.Def_SubspaceConv_Supplement_incidence

set_option autoImplicit false

universe u

namespace SubspaceConv.Supplement

/-- **Theorem 2**, Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), p.2 (PDF p.3). Under the coefficient assumption of theorem 1,
`I_n^{a,b}` and its transpose take `O_q(S log S)` arithmetic operations, where
`S = |Gr_q(n, a)| + |Gr_q(n, b)|` is the total input and output length.

**Formalization Note** The model is the published `SubspaceConv.LinSLP` of Theorem 1 (free input
reads and zero; every addition, subtraction, integer scaling and multiplication by `p⁻¹` costs
one operation). `O_q`: one real constant `C`, depending only on the field `F` (chosen before
`n, a, b`), bounds both programs for every `0 ≤ a ≤ b ≤ n`, boundary cases included; `log` is the
natural logarithm, and `S ≥ 2` always. "Under the coefficient assumption of theorem 1": one
well-formed program, evaluated over every commutative ring `A` with an element `pinv`,
`p · pinv = 1` (`p = ringChar F`), computes `I_n^{a,b} f` for every table `f : Gr(n,a) → A`; a
second computes the transpose on every table `g : Gr(n,b) → A`. -/
theorem theorem_2 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℝ, ∀ n a b : ℕ, a ≤ b → b ≤ n →
      ∃ (P : LinSLP (Gr F n a) (Gr F n b)) (Q : LinSLP (Gr F n b) (Gr F n a)),
        P.WellFormed ∧ Q.WellFormed ∧
        (P.cost : ℝ) ≤ C * ((Fintype.card (Gr F n a) + Fintype.card (Gr F n b) : ℕ) : ℝ) *
          Real.log ((Fintype.card (Gr F n a) + Fintype.card (Gr F n b) : ℕ) : ℝ) ∧
        (Q.cost : ℝ) ≤ C * ((Fintype.card (Gr F n a) + Fintype.card (Gr F n b) : ℕ) : ℝ) *
          Real.log ((Fintype.card (Gr F n a) + Fintype.card (Gr F n b) : ℕ) : ℝ) ∧
        ∀ (A : Type u) [CommRing A] (pinv : A), (ringChar F : A) * pinv = 1 →
          (∀ f : Gr F n a → A, P.eval pinv f = incidence a b f) ∧
          ∀ g : Gr F n b → A, Q.eval pinv g = incidenceT a b g := by sorry

end SubspaceConv.Supplement
