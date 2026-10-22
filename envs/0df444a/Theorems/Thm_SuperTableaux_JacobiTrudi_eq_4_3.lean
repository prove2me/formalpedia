-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_eq_4_3
-- name    : SuperTableaux.JacobiTrudi.eq_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:47.893797+00:00
-- url     : https://prove2.me/theorems/103f1c14-5ddc-4e8c-b776-4377f05e5227
-- title:
--   (4.3), p. 24 — $K_{\lambda\mu}=K_{\lambda+(d^n)\,\mu+(d^n)}$ and $K_{\lambda\mu}=0$ unless $\lambda\ge\mu$
-- statement:
--   Let $n\ge1$ and $\lambda,\mu\in\mathbb Z^n_+$, and let $K_{\lambda\mu}$ be the number of rational $[n]$-semistandard tableaux of shape $\lambda$ with content $\mu$. Then
--
--   1. for every integer $d>0$,
--   $$K_{\lambda\mu}=K_{\lambda+(d^n)\,\mu+(d^n)};$$
--   2. $K_{\lambda\mu}=0$ unless $\lambda\ge\mu$, where $\ge$ is the order of p. 23: $\lambda>\mu$ iff for some $i$, $\lambda_k=\mu_k$ for $k<i$ and $\lambda_i>\mu_i$.
--
--   Together these say that the rational Kostka matrix is the ordinary one shifted, and is unitriangular-supported with respect to the lexicographic order; this is what turns the $H$-expansion into a triangular system in the proof of Theorem 4.5.
--
--   **Formalization Note** The order on $\mathbb Z^n_+$ is Mathlib's lexicographic order `toLex` on `Fin n → ℤ` (first differing entry larger), which is exactly the paper's "reverse lexicographic ordering" as defined on p. 23. The page's further remark that $K_{\lambda+(d^n)\,\mu+(d^n)}$ is the ordinary Kostka number when both shifts are partitions is not a separate clause: for a shape with nonnegative parts, a rational $[n]$-semistandard tableau is, by definition, an ordinary $[n]$-semistandard tableau.
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, p. 24, (4.3) and the sentence following it

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting

namespace SuperTableaux.JacobiTrudi
theorem eq_4_3 (n : ℕ) (hn : 0 < n) (la mu : GenPartition n) :
    (∀ d : ℕ, 0 < d → kostka (shift la d) (shift mu d) = kostka la mu) ∧
      (kostka la mu ≠ 0 → toLex mu.1 ≤ toLex la.1) := by sorry
end SuperTableaux.JacobiTrudi
