-- Prove2me | Theorems.Thm_VanderbeiLP_Simplex_lex_pivot_increases_perturbed_objective
-- name    : VanderbeiLP.Simplex.lex_pivot_increases_perturbed_objective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-03T20:31:05.140094+00:00
-- url     : https://prove2.me/theorems/4697f23a-3f4a-477a-91db-f33b8c7b81ad
-- title:
--   A lexicographic pivot strictly increases the perturbed objective
-- statement:
--   Fix dictionaries $D_0,D,D'$ for the same constraint matrix, a right-hand side $b$, and objective coefficients $c$. Write $q_D(i)$ for the symbolic perturbed right-hand-side coefficient vector. Assume all basic rows of $D$ are strictly positive in lexicographic order and $D\to D'$ is a lexicographic simplex pivot. The coefficient vector of the perturbed objective value is
--   $$
--   Z(D)=\sum_{i\in B_D}\widetilde c_i q_D(i).
--   $$
--   Then
--   $$
--   Z(D)<_{\mathrm{lex}}Z(D').
--   $$
--   Here the objective coefficient of a slack variable is zero. This makes precise the nondegenerate objective improvement used with Vanderbei's Theorem 3.2: for entering index $k$ and leaving index $l$, the basis-exchange identities give
--   $$
--   Z(D')-Z(D)=\frac{\bar c_k}{\bar a_{lk}}q_D(l).
--   $$
--   Both scalar coefficients are positive, and the leaving row is lexicographically positive. This local result provides the strictly increasing potential for the termination argument.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, Chapter 3, pp. 28–30, §3.3 and proof of Theorem 3.2; pivot algebra of Chapter 2, p. 15. https://nibmehub.com/opac-service/pdf/read/Linear%20Programming-%204th%20edition-%202014.pdf

import Definitions.Def_VanderbeiLP_Simplex_PivotRules

theorem VanderbeiLP.Simplex.lex_pivot_increases_perturbed_objective
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (D₀ D D' : VanderbeiLP.Simplex.Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hpos : ∀ i ∈ D.B, toLex (0 : Fin (m + 1) → ℝ) <
      toLex (VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b i))
    (hpivot : VanderbeiLP.Simplex.Dictionary.IsLexPivot D₀ b c D D') :
    toLex (∑ i ∈ D.B, VanderbeiLP.Simplex.extCost c i •
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b i) <
    toLex (∑ i ∈ D'.B, VanderbeiLP.Simplex.extCost c i •
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ D' b i) := by sorry
