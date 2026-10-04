-- Prove2me | Theorems.Thm_VanderbeiLP_Simplex_lex_pivot_preserves_positive_rows
-- name    : VanderbeiLP.Simplex.lex_pivot_preserves_positive_rows
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-03T20:30:46.696226+00:00
-- url     : https://prove2.me/theorems/68f5a12f-f0c8-47a5-91b2-72ab1e2f712e
-- title:
--   Lexicographic pivots preserve positive perturbed basic rows
-- statement:
--   Fix dictionaries $D_0,D,D'$ for the same constraint matrix and fix the right-hand side $b$ and objective coefficients $c$. Let $q_D(i)$ be the coefficient vector of the symbolic perturbed right-hand side of row $i$, with the perturbation symbols attached to the basic rows of $D_0$ in increasing index order. If every basic row of $D$ is strictly positive in lexicographic order and $D\to D'$ is a lexicographic simplex pivot, then
--   $$
--   q_{D'}(i)>_{\mathrm{lex}}0\quad\text{for every }i\in B_{D'}.
--   $$
--   This is the invariant used in the perturbation proof of Theorem 3.2. The lexicographic ratio test preserves nonnegative rows; the perturbation matrix is a change-of-basis matrix between two bases, so its rows cannot vanish. For rows with positive entering coefficient the normalized perturbation rows are distinct, ruling out a zero row after subtracting the minimum ratio. The entering row is the positive leaving row divided by a positive pivot coefficient. No reachability assumption on $D$ is needed.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, Chapter 3, pp. 28–30, §3.3 and proof of Theorem 3.2; pivot algebra of Chapter 2, p. 15. https://nibmehub.com/opac-service/pdf/read/Linear%20Programming-%204th%20edition-%202014.pdf

import Definitions.Def_VanderbeiLP_Simplex_PivotRules

theorem VanderbeiLP.Simplex.lex_pivot_preserves_positive_rows
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (D₀ D D' : VanderbeiLP.Simplex.Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hpos : ∀ i ∈ D.B, toLex (0 : Fin (m + 1) → ℝ) <
      toLex (VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b i))
    (hpivot : VanderbeiLP.Simplex.Dictionary.IsLexPivot D₀ b c D D') :
    ∀ i ∈ D'.B, toLex (0 : Fin (m + 1) → ℝ) <
      toLex (VanderbeiLP.Simplex.Dictionary.lexRow D₀ D' b i) := by sorry
