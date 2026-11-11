-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_lemma_2_23
-- name    : SparseLowFactors.BoundedDeg.lemma_2_23
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:23:38.8671+00:00
-- url     : https://prove2.me/theorems/64a9d474-c51a-4470-9ac8-23d8f89a1252
-- title:
--   Lemma 2.23 — a factor $g$ of $f$ gives the monic factor $\hat g$ of the normalization $\hat f$
-- statement:
--   Let $f=\sum_{i=0}^df_i(X)Y^i$ and $g=\sum_{i=0}^tg_i(X)Y^i$ in $F[X,Y]$ with $f_d\neq0$, $g_t\neq0$, and $g\mid f$. Let
--   $$\hat f=f(X,Y/f_d)\,f_d^{\,d-1},\qquad \hat g=\frac{g(X,Y/f_d)\,f_d^{\,t}}{g_t}=\sum_{i=0}^t\frac{g_i\,f_d^{\,t-i}}{g_t}\,Y^i .$$
--   Then $\hat g\in F[X,Y]$ and $\hat g\mid\hat f$ in $F[X,Y]$.
--
--   Factors of $f$ thus appear, after normalization, among the monic factors of $\hat f$, which Lemma 3.1 lists.
--
--   **Formalization Note** "$\hat g\in F[X,Y]$" is stated as: there is a polynomial $\hat g$ with $g_t\cdot\hat g=\sum_ig_if_d^{\,t-i}Y^i$ (unique, as $F[X]$ is a domain); $\hat f$ is the Normalization definition.
--
--   Differences from the source:
--   - encoding: ĝ = g(X, Y/f_d) f_d^t / g_t as a rational function → a polynomial ĝ with g_t · ĝ = Σ_i g_i f_d^{t−i} Y^i; reason: the rational expression and its coefficient formula are the same; existence of the polynomial is the claim "ĝ ∈ F[X, Y]"
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 22, Lemma 2.23

import Mathlib
import Definitions.Def_SparseLowFactors_BoundedDeg_Normalization

open Polynomial

namespace SparseLowFactors.BoundedDeg

theorem lemma_2_23 (F : Type) [Field F] (n : ℕ) (f g : Polynomial (MvPolynomial (Fin n) F))
    (hf : f.leadingCoeff ≠ 0) (hg : g.leadingCoeff ≠ 0) (hdiv : g ∣ f) :
    ∃ ghat : Polynomial (MvPolynomial (Fin n) F),
      C g.leadingCoeff * ghat =
        ∑ i ∈ Finset.range (g.natDegree + 1),
          C (g.coeff i * f.leadingCoeff ^ (g.natDegree - i)) * X ^ i ∧
      ghat ∣ normalize f := by sorry

end SparseLowFactors.BoundedDeg
