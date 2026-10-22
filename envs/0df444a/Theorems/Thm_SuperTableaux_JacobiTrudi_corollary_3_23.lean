-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_corollary_3_23
-- name    : SuperTableaux.JacobiTrudi.corollary_3_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:13.000789+00:00
-- url     : https://prove2.me/theorems/b40e1804-6d9d-4350-8448-d26c24faadff
-- title:
--   Corollary 3.23, p. 19 — $\sum_{\lambda}a_\lambda S^{\mathcal A/\mathcal B}_\lambda$ over level $n$ is well defined, with unique coefficients
-- statement:
--   Let $\mathcal A,\mathcal B$ be linearly ordered, at most countable, $\mathbb Z_2$-graded sets, $n\ge1$, and $a_\lambda\in\mathbb Z$ for $\lambda\in\mathbb Z^n_+$. Then
--
--   1. the possibly infinite sum
--   $$\sum_{\lambda\in\mathbb Z^n_+}a_\lambda\,S^{\mathcal A/\mathcal B}_\lambda$$
--   converges in $\mathbb Z[[x_{\mathcal A},x_{\mathcal B}^{-1}]]$;
--   2. if it is $0$, then $a_\lambda=0$ for every $\lambda\in\mathscr P_{\mathcal A/\mathcal B,n}$ (every $\lambda$ with $SST_{\mathcal A/\mathcal B}(\lambda)\ne\emptyset$), i.e. the coefficients $a_\lambda$, $\lambda\in\mathscr P_{\mathcal A/\mathcal B,n}$, are uniquely determined.
--
--   This is the coefficient-comparison tool that finishes the proof of Theorem 4.5.
--
--   **Formalization Note** Summing over all of $\mathbb Z^n_+$ is the paper's sum over $\mathscr P_{\mathcal A/\mathcal B,n}$, because $S^{\mathcal A/\mathcal B}_\lambda=0$ off that set (its coefficients count elements of the empty set). Convergence is `Summable`/`HasSum` in the coefficientwise topology; uniqueness is stated as "a convergent sum equal to $0$ has zero coefficients on $\mathscr P_{\mathcal A/\mathcal B,n}$", equivalent by linearity.
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, p. 19, Corollary 3.23

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting
open scoped MvPowerSeries.WithPiTopology

namespace SuperTableaux.JacobiTrudi
theorem corollary_3_23 {A B : Type*} [LinearOrder A] [Countable A] [LinearOrder B] [Countable B]
    (oddA : A → Bool) (oddB : B → Bool) (n : ℕ) (hn : 0 < n) (a : GenPartition n → ℤ) :
    Summable (fun la : GenPartition n => a la • charAB oddA oddB la) ∧
      (HasSum (fun la : GenPartition n => a la • charAB oddA oddB la) 0 →
        ∀ la, Nonempty (ABTab oddA oddB la) → a la = 0) := by sorry
end SuperTableaux.JacobiTrudi
