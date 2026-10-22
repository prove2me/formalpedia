-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_remark_3_19
-- name    : SuperTableaux.JacobiTrudi.remark_3_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:58.630406+00:00
-- url     : https://prove2.me/theorems/e4e2b9d8-e1dc-4ae7-843e-0837778a9de6
-- title:
--   Remark 3.19, p. 18 — infinite combinations of $S_\lambda(x_{\mathcal A})S_\mu(x_{\mathcal B}^{-1})$ are well defined with unique coefficients
-- statement:
--   Let $\mathcal A,\mathcal B$ be linearly ordered, at most countable, $\mathbb Z_2$-graded sets, and let $c_{\lambda\mu}\in\mathbb Z$ for $\lambda\in\mathscr P_{\mathcal A}$, $\mu\in\mathscr P_{\mathcal B}$. Then
--
--   1. the possibly infinite sum
--   $$\sum_{\lambda\in\mathscr P_{\mathcal A},\,\mu\in\mathscr P_{\mathcal B}}c_{\lambda\mu}\,S_\lambda(x_{\mathcal A})S_\mu(x_{\mathcal B}^{-1})$$
--   converges in $\mathbb Z[[x_{\mathcal A},x_{\mathcal B}^{-1}]]$ (each monomial occurs in only finitely many terms);
--   2. if this sum is $0$, then $c_{\lambda\mu}=0$ for all $\lambda,\mu$; that is, the coefficients are uniquely determined.
--
--   Here $S_\mu(x_{\mathcal B}^{-1})$ is the character of $SST_{\mathcal B}(\mu)$ in the variables $x_b^{-1}$. This is the uniqueness principle behind Proposition 3.20 and Corollary 3.23.
--
--   **Formalization Note** "Well-defined" is `Summable` and the sum is a `HasSum` in the coefficientwise topology of `MvPowerSeries (A ⊕ B) ℤ` (with $\mathbb Z$ discrete); uniqueness of coefficients is stated as: a convergent sum equal to $0$ has all coefficients $0$, which is equivalent by linearity. $S_\lambda(x_{\mathcal A})$ and $S_\mu(x_{\mathcal B}^{-1})$ are the tableau generating functions placed on the variables `Sum.inl a` ($x_a$) and `Sum.inr b` ($x_b^{-1}$).
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, p. 18, Remark 3.19

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting
open scoped MvPowerSeries.WithPiTopology

namespace SuperTableaux.JacobiTrudi
theorem remark_3_19 {A B : Type*} [LinearOrder A] [Countable A] [LinearOrder B] [Countable B]
    (oddA : A → Bool) (oddB : B → Bool)
    (c : {la : YoungDiagram // Nonempty (SSF oddA la)} ×
      {mu : YoungDiagram // Nonempty (SSF oddB mu)} → ℤ) :
    Summable (fun p : {la : YoungDiagram // Nonempty (SSF oddA la)} ×
        {mu : YoungDiagram // Nonempty (SSF oddB mu)} =>
        c p • (charAinl B oddA p.1.1 * charBinr A oddB p.2.1)) ∧
      (HasSum (fun p : {la : YoungDiagram // Nonempty (SSF oddA la)} ×
          {mu : YoungDiagram // Nonempty (SSF oddB mu)} =>
          c p • (charAinl B oddA p.1.1 * charBinr A oddB p.2.1)) 0 → c = 0) := by sorry
end SuperTableaux.JacobiTrudi
