-- Prove2me | Theorems.Thm_ResultantVNP_connected_binomial_resultant
-- name    : ResultantVNP.connected_binomial_resultant
-- status  : Proved
-- author  : @gjindal
-- created : 2026-11-14T13:20:59.19722+00:00
-- url     : https://prove2.me/theorems/91d5cbf8-5a53-4b89-8d0e-983b58d00a6d
-- title:
--   Resultant and squarefree coefficient of a connected balanced binomial system
-- statement:
--   Let f and g map {1,…,n} to itself, with n ≥ 1. Suppose the directed multigraph with two arcs i → f(i), g(i) at each vertex has indegree two at each vertex and is connected after forgetting arc directions. For any normalized multivariate resultant system, let P(t) be the resultant of the quadratic forms x_i² − t_i x_{f(i)}x_{g(i)}. There is an integer c ≥ 1 such that
--
--   $$P(\mathbf t)=(1-\prod_{i=1}^n t_i)^c,\qquad [t_1\cdots t_n]P=-c.$$
--
--   In particular, this squarefree coefficient is a negative integer. Loops and repeated arcs are allowed; all arcs are counted with multiplicity.
-- source:
--   The binomial-system step in the proof of Theorem 3.5 in Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 paper #1103; generalized to any connected balanced two-outdegree directed multigraph.

import Mathlib
import Definitions.Def_ResultantVNP_ResultantSystem

theorem ResultantVNP.connected_binomial_resultant (𝓡 : ResultantVNP.ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (f g : Fin n → Fin n)
    (hb : ∀ v,(Finset.univ.filter (fun u => f u = v)).card +
      (Finset.univ.filter (fun u => g u = v)).card = 2)
    (hc : ∀ u v,Relation.ReflTransGen
      (fun a b => f a = b ∨ g a = b ∨ f b = a ∨ g b = a) u v) :
    let P : MvPolynomial (Fin n) ℂ :=
      MvPolynomial.aeval (fun v : ResultantVNP.CoeffVar (fun _ : Fin n => 2) =>
        (MvPolynomial.X v.1 ^ 2 - MvPolynomial.C (MvPolynomial.X v.1) *
          MvPolynomial.X (f v.1) * MvPolynomial.X (g v.1) :
            MvPolynomial (Fin n) (MvPolynomial (Fin n) ℂ)).coeff v.2.1)
        (MvPolynomial.map (Int.castRingHom ℂ) (𝓡.res (fun _ => 2)))
    ∃ c : ℕ, 1 ≤ c ∧ P = (1 - ∏ i : Fin n,(MvPolynomial.X i : MvPolynomial (Fin n) ℂ)) ^ c ∧
      P.coeff (Finsupp.indicator Finset.univ (fun _ _ => 1)) = -(c : ℂ) := by sorry
