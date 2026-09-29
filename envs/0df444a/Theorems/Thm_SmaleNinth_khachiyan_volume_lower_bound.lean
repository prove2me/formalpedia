-- Prove2me | Theorems.Thm_SmaleNinth_khachiyan_volume_lower_bound
-- name    : SmaleNinth.khachiyan_volume_lower_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-06T22:08:21.100301+00:00
-- url     : https://prove2.me/theorems/cce746fb-53b9-4a98-970e-63a07319a543
-- title:
--   Volume lower bound for Khachiyan's perturbed-and-boxed system
-- statement:
--   **The perturbed-and-boxed system has volume bounded below when it is nonempty.**
--
--   With $\varepsilon = 1/\bigl(2(n+1)(n+1)!\,U^{n+1}\bigr)$, $M = n!\,U^{n}+1$ and $v = \bigl(\varepsilon/(nU)\bigr)^{n}$, the assertion is that if the perturbed-and-boxed polyhedron is nonempty then its Lebesgue volume is at least $v$. In particular it is full-dimensional.
--
--   This is the second thing the ellipsoid method needs. Halving the volume of an enclosing ellipsoid terminates only if a nonempty feasible set cannot be arbitrarily thin; a set of measure zero would never be detected. The original system $Ax\ge b$ offers no such guarantee — it can be a single point, or a lower-dimensional face — and the perturbation by $\varepsilon$ is exactly what fattens it.
--
--   **The argument.** Suppose the perturbed-and-boxed system has a solution. By the feasibility equivalence, the original system $Ax\ge b$ then has a solution $x_0$, and by the Cramer–Hadamard size bound one with $\|x_0\|_\infty \le n!\,U^{n} = M-1$. Consider the cube of side $\varepsilon/(nU)$ centred at $x_0$. Every point $x$ of that cube satisfies $\|x-x_0\|_\infty \le \varepsilon/(2nU)$, so for each original row,
--
--   $$(Ax)_i \;\ge\; (Ax_0)_i - \sum_{j=1}^{n} |A_{ij}|\,|x_j - x_{0,j}| \;\ge\; b_i - n\,U\cdot\frac{\varepsilon}{2nU} \;>\; b_i - \varepsilon,$$
--
--   and the box constraints hold because $\|x_0\|_\infty \le M-1$ leaves a margin of $1$, which comfortably exceeds the cube's half-width. So the cube is contained in the polyhedron, and the volume is at least that of the cube, namely $\bigl(\varepsilon/(nU)\bigr)^{n} = v$.
-- source:
--   L. G. Khachiyan, A polynomial algorithm in linear programming, Soviet Math. Doklady 20 (1979) 191-194; B. Korte, J. Vygen, Combinatorial Optimization, 6th ed., Springer 2018, Sections 4.4-4.5; D. Bertsimas, J. N. Tsitsiklis, Introduction to Linear Optimization, Athena Scientific 1997, Section 8.4 (full-dimensionality and volume of the perturbed system). One of the four claims of SmaleNinth.khachiyan_perturbation_bounds.

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_SmaleNinth_Khachiyan

open Matrix LinearOptimization

theorem SmaleNinth.khachiyan_volume_lower_bound {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    (polyhedron (SmaleNinth.khachiyanSystemA A)
        (SmaleNinth.khachiyanSystemb n U b)).Nonempty →
      ENNReal.ofReal (SmaleNinth.khachiyanVolLB n U) ≤
        MeasureTheory.volume (polyhedron (SmaleNinth.khachiyanSystemA A)
          (SmaleNinth.khachiyanSystemb n U b)) := by sorry
