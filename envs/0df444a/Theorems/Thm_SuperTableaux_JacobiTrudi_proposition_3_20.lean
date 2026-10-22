-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_proposition_3_20
-- name    : SuperTableaux.JacobiTrudi.proposition_3_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:55.375076+00:00
-- url     : https://prove2.me/theorems/cf31dd7a-da81-4aed-9ab4-51630e430cc4
-- title:
--   Proposition 3.20, p. 19 — $S_\lambda(x_{\mathcal A},x_{\mathcal B})=\sum_{\mu,\nu\in\mathscr P_n}c^\lambda_{\mu\nu^*}S_\mu(x_{\mathcal A})S_\nu(x_{\mathcal B}^{-1})$
-- statement:
--   Let $\mathcal A,\mathcal B$ be linearly ordered, at most countable, $\mathbb Z_2$-graded sets, $n\ge1$, and $\lambda\in\mathscr P_{\mathcal A/\mathcal B,n}$, i.e. $\lambda\in\mathbb Z^n_+$ with $SST_{\mathcal A/\mathcal B}(\lambda)\ne\emptyset$. Then
--   $$S_\lambda(x_{\mathcal A},x_{\mathcal B})=\sum_{\mu,\nu\in\mathscr P_n}c^\lambda_{\mu\,\nu^*}\,S_\mu(x_{\mathcal A})\,S_\nu(x_{\mathcal B}^{-1}),$$
--   where $\nu^*=(-\nu_n,\dots,-\nu_1)$ and $c^\lambda_{\mu\nu}=N^{\lambda+((p+q)^n)}_{\mu+(p^n)\,\nu+(q^n)}$ ($p,q$ large) are the rational Littlewood–Richardson coefficients of (3.7). The sum is in general infinite and converges coefficientwise.
--
--   This branching rule expresses the A/B-characters through products of super Schur functions in $x_{\mathcal A}$ and $x_{\mathcal B}^{-1}$; for $\lambda=0_n$ it gives $S_{0_n}=\sum_{\lambda\in\mathscr P_n}S_\lambda(x_{\mathcal A})S_\lambda(x_{\mathcal B}^{-1})$ (Example 3.21).
--
--   **Formalization Note** The sum is a `HasSum` in the coefficientwise topology. Partitions in $\mathscr P_n$ are generalized partitions of level $n$ with nonnegative parts, converted to Young diagrams. $c^\lambda_{\mu\nu}$ is computed from Littlewood–Richardson tableaux at $p=q=\sum_i(|\lambda_i|+|\mu_i|+|\nu_i|)+1$ (see the definitions item; by Lemma 3.7 any $p,q$ making the three shapes partitions give the same number).
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, p. 19, Proposition 3.20 (with (3.7), p. 14, and LR tableaux, p. 6)

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting
open scoped MvPowerSeries.WithPiTopology

namespace SuperTableaux.JacobiTrudi
theorem proposition_3_20 {A B : Type*} [LinearOrder A] [Countable A] [LinearOrder B] [Countable B]
    (oddA : A → Bool) (oddB : B → Bool) (n : ℕ) (hn : 0 < n) (la : GenPartition n)
    (hla : Nonempty (ABTab oddA oddB la)) :
    HasSum (fun p : {mu : GenPartition n // ∀ i, 0 ≤ mu.1 i} ×
        {nu : GenPartition n // ∀ i, 0 ≤ nu.1 i} =>
        (lrc la p.1.1 (star p.2.1) : ℤ) •
          (charAinl B oddA (toYD p.1.1) * charBinr A oddB (toYD p.2.1)))
      (charAB oddA oddB la) := by sorry
end SuperTableaux.JacobiTrudi
