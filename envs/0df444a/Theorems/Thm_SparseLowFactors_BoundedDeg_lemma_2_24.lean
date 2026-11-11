-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_lemma_2_24
-- name    : SparseLowFactors.BoundedDeg.lemma_2_24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:23:39.218591+00:00
-- url     : https://prove2.me/theorems/2cf762d8-f3b8-4124-9f65-cbe3b8d90a6c
-- title:
--   Lemma 2.24 — a factor $g$ of $f$ gives the reversed-monic factor $\tilde g$ of the reverse normalization $\tilde f$
-- statement:
--   Let $f=\sum_{i=0}^df_i(X)Y^i$ and $g=\sum_{i=0}^tg_i(X)Y^i$ in $F[X,Y]$ with $f_0\neq0$, $g_0\neq0$, and $g\mid f$. Let
--   $$\tilde f=\frac{f(X,Yf_0)}{f_0},\qquad \tilde g=\frac{g(X,Yf_0)}{g_0}=\sum_{i=0}^t\frac{g_i\,f_0^{\,i}}{g_0}\,Y^i .$$
--   Then $\tilde g\in F[X,Y]$ and $\tilde g\mid\tilde f$ in $F[X,Y]$.
--
--   This is the counterpart of Lemma 2.23 used when the constant coefficient in $Y$ is the sparser one.
--
--   **Formalization Note** "$\tilde g\in F[X,Y]$" is stated as: there is a polynomial $\tilde g$ with $g_0\cdot\tilde g=\sum_ig_if_0^{\,i}Y^i$; $\tilde f$ is the Normalization definition.
--
--   Differences from the source:
--   - encoding: g̃ = g(X, Y f_0)/g_0 as a rational function → a polynomial g̃ with g_0 · g̃ = Σ_i g_i f_0^i Y^i; reason: the rational expression and its coefficient formula are the same; existence of the polynomial is the claim "g̃ ∈ F[X, Y]"
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 22, Lemma 2.24

import Mathlib
import Definitions.Def_SparseLowFactors_BoundedDeg_Normalization

open Polynomial

namespace SparseLowFactors.BoundedDeg

theorem lemma_2_24 (F : Type) [Field F] (n : ℕ) (f g : Polynomial (MvPolynomial (Fin n) F))
    (hf : f.coeff 0 ≠ 0) (hg : g.coeff 0 ≠ 0) (hdiv : g ∣ f) :
    ∃ gtil : Polynomial (MvPolynomial (Fin n) F),
      C (g.coeff 0) * gtil =
        ∑ i ∈ Finset.range (g.natDegree + 1), C (g.coeff i * f.coeff 0 ^ i) * X ^ i ∧
      gtil ∣ revNormalize f := by sorry

end SparseLowFactors.BoundedDeg
