-- Prove2me | Theorems.Thm_SmaleNinth_khachiyan_feasibility_equiv
-- name    : SmaleNinth.khachiyan_feasibility_equiv
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-06T22:08:20.29739+00:00
-- url     : https://prove2.me/theorems/23bae642-a15a-47fb-996c-d559fdfe272c
-- title:
--   Khachiyan's perturbed-and-boxed system is feasibility-equivalent
-- statement:
--   **The perturbed-and-boxed system is feasibility-equivalent to the original.**
--
--   For an integer system $Ax\ge b$ in $n\ge1$ variables with all entries bounded by $U\ge1$, put $\varepsilon = 1/\bigl(2(n+1)(n+1)!\,U^{n+1}\bigr)$ and $M = n!\,U^{n}+1$. The assertion is
--
--   $$\exists x,\ Ax \ge b \qquad\Longleftrightarrow\qquad \exists x,\ Ax \ge b-\varepsilon\mathbf 1,\ -M\mathbf 1\le x\le M\mathbf 1 .$$
--
--   Neither direction is formal. Relaxing the right-hand side makes the system *easier*, and boxing it makes it *harder*, and the content is that with these particular constants the two changes cancel exactly.
--
--   **The easy direction is the box.** If $Ax\ge b$ is solvable then it has a solution of sup-norm at most $n!\,U^{n} = M-1$, by the Cramer–Hadamard size bound `SmaleNinth.integer_polyhedron_solution_bound`. That solution lies in the box, and it satisfies the relaxed inequalities a fortiori.
--
--   **The other direction is Farkas.** If $Ax\ge b$ is infeasible then by Farkas' lemma there is a rational certificate $y\ge0$ with $y^{\mathsf T}A=0$ and $y^{\mathsf T}b>0$. Taking $y$ to be a basic solution of the certificate system and applying Cramer's rule bounds its entries, so $y^{\mathsf T}b \ge 1/\Delta$ for an explicit determinant $\Delta$, while the perturbation contributes at most $\varepsilon\,\|y\|_1$. The constant $\varepsilon$ is chosen precisely so that the perturbation cannot overcome the gap, and the relaxed system is infeasible too. The boxing is then irrelevant in this direction.
--
--   Why it matters: the ellipsoid method cannot be run on $Ax\ge b$ directly, because that set may be lower-dimensional and unbounded. This lemma is what licenses replacing it by a set that is bounded, full-dimensional, and has the same answer.
-- source:
--   L. G. Khachiyan, A polynomial algorithm in linear programming, Soviet Math. Doklady 20 (1979) 191-194; B. Korte, J. Vygen, Combinatorial Optimization, 6th ed., Springer 2018, Sections 4.4-4.5; D. Bertsimas, J. N. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 8.4 (full-dimensionality and volume of the perturbed system). One of the four claims of SmaleNinth.khachiyan_perturbation_bounds.

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_SmaleNinth_Khachiyan

open Matrix LinearOptimization

theorem SmaleNinth.khachiyan_feasibility_equiv {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    (polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ))).Nonempty ↔
      (polyhedron (SmaleNinth.khachiyanSystemA A)
        (SmaleNinth.khachiyanSystemb n U b)).Nonempty := by sorry
