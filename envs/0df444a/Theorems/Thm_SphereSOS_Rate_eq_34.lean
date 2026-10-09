-- Prove2me | Theorems.Thm_SphereSOS_Rate_eq_34
-- name    : SphereSOS.Rate.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:20:09.422795+00:00
-- url     : https://prove2.me/theorems/b0192466-aa03-4337-9800-b997237e04b0
-- title:
--   (34), p. 16 — $\|f_{2k}\|_\infty\le\|f\|_\infty(2n)!\,[1+(2n)!]^k\le\|f\|_\infty(2n)!\,[1+(2n)!]^n$
-- statement:
--   Let $f$ be a homogeneous polynomial of degree $2n$ in $d$ variables with harmonic decomposition $f=\sum_{k=0}^n\|x\|^{2(n-k)}f_{2k}$, and let $|f|\le M$ on $S^{d-1}$. Then for every $k=0,\dots,n$ and $x\in S^{d-1}$,
--   $$|f_{2k}(x)|\le M\,(2n)!\,[1+(2n)!]^k\le M\,(2n)!\,[1+(2n)!]^n.$$
--
--   Hence $B_{2n}\le(2n)!\,[1+(2n)!]^n$, an explicit dimension-free value of the constant in Proposition 5.
--
--   **Formalization Note** Both inequalities of (34) are stated. The index $k$ is the harmonic degree $2k$, as in the induction (33) that proves (34), which starts from $f_0$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 16, (34) and the sentence after it

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting

namespace SphereSOS.Rate

theorem eq_34 (n d : ℕ) (f : MvPolynomial (Fin d) ℝ)
    (h : Fin (n + 1) → MvPolynomial (Fin d) ℝ)
    (hf : f.IsHomogeneous (2 * n)) (hdecomp : IsHarmonicDecomp n f h)
    (M : ℝ) (hM : ∀ x ∈ sphere d, |MvPolynomial.eval x f| ≤ M) :
    ∀ j x, x ∈ sphere d →
      |MvPolynomial.eval x (h j)| ≤
        M * ((2 * n).factorial : ℝ) * (1 + ((2 * n).factorial : ℝ)) ^ (j : ℕ) ∧
      |MvPolynomial.eval x (h j)| ≤
        M * ((2 * n).factorial : ℝ) * (1 + ((2 * n).factorial : ℝ)) ^ n := by sorry

end SphereSOS.Rate
