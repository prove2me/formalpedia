-- Prove2me | Theorems.Thm_VanderbeiLP_Simplex_lex_pivot_perturbed_objective_basis_exchange
-- name    : VanderbeiLP.Simplex.lex_pivot_perturbed_objective_basis_exchange
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-03T21:11:15.092973+00:00
-- url     : https://prove2.me/theorems/9d2868df-85d1-4f14-976f-ad01afd2e562
-- title:
--   Basis exchange formula for the perturbed objective vector
-- statement:
--   For an entering index k and a leaving index l, the perturbed objective vector changes under a basis exchange by (reduced cost of k divided by the pivot coefficient in row l) times the perturbed row of l. This is the pivot identity underlying strict objective improvement for the lexicographic simplex rule.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, Chapter 2, p. 15 and Chapter 3, pp. 28–30.

import Definitions.Def_VanderbeiLP_Simplex_PivotRules

theorem VanderbeiLP.Simplex.lex_pivot_perturbed_objective_basis_exchange
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (D₀ D D' : VanderbeiLP.Simplex.Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (k l : Fin (n + m))
    (henter : D.IsEnteringCandidate c k)
    (hleave : VanderbeiLP.Simplex.Dictionary.IsLexLeaving D₀ D b k l)
    (hB : D'.B = insert k (D.B.erase l)) :
    (∑ i ∈ D'.B, VanderbeiLP.Simplex.extCost c i •
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ D' b i) =
    (∑ i ∈ D.B, VanderbeiLP.Simplex.extCost c i •
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b i) +
      (D.cbar c k / D.abar l k) • VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b l := by sorry
