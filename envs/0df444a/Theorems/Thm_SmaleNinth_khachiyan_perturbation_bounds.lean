-- Prove2me | Theorems.Thm_SmaleNinth_khachiyan_perturbation_bounds
-- name    : SmaleNinth.khachiyan_perturbation_bounds
-- status  : Proved
-- author  : @ORdos
-- created : 2026-09-06T15:26:27.384116+00:00
-- url     : https://prove2.me/theorems/a0f08c86-0f84-4e27-ab14-f664375f04a2
-- title:
--   Khachiyan's perturbation bounds
-- statement:
--   The ellipsoid method decides a linear system by repeatedly halving the volume of an ellipsoid known to contain the feasible set. For this to terminate, the set must be enclosed in a ball of known radius; for a negative answer to be conclusive, the set must be known to have volume above an explicit floor whenever it is nonempty. A system with integer data satisfies neither condition as given — it may be unbounded, and it may be feasible yet of measure zero. This theorem supplies the standard remedy and its four quantitative guarantees.
--
--   Let $U \ge 1$, let $A \in \mathbb{Z}^{m \times n}$ and $b \in \mathbb{Z}^m$ have all entries bounded by $U$ in absolute value, and let $n \ge 1$. Write $P = \{x \in \mathbb{R}^n \mid Ax \ge b\}$ for the original solution set, and let
--
--   $$\widehat P \;=\; \bigl\{\, x \in \mathbb{R}^n \;\bigm|\; Ax \ge b - \varepsilon\mathbf{1}, \ \ -M \le x_j \le M \ \text{ for all } j \,\bigr\}$$
--
--   be the perturbed-and-boxed solution set, with $\varepsilon = \bigl(2(n+1)(n+1)!\,U^{n+1}\bigr)^{-1}$ and $M = n!\,U^n + 1$. Then:
--
--   1. **Feasibility is preserved in both directions:** $P \ne \emptyset$ if and only if $\widehat P \ne \emptyset$. Relaxing the inequalities by $\varepsilon$ cannot create feasibility, and imposing the box cannot destroy it.
--   2. **Boundedness:** $\widehat P$ is bounded, in the elementary sense that some $K$ bounds every coordinate of every one of its points.
--   3. **An explicit enclosure:** $\widehat P$ is contained in the ball of radius $r = (n+1)M$ centred at the origin.
--   4. **A volume floor:** if $\widehat P$ is nonempty then its Lebesgue measure is at least $v = \bigl(\varepsilon/(nU)\bigr)^{n}$.
--
--   **Reading the fourth claim.** The bound is non-strict and conditional: nothing is asserted when $\widehat P$ is empty, in which case its measure is of course $0$. Since $v > 0$ under the standing hypotheses, the claim implies that a nonempty $\widehat P$ is full-dimensional — the property the ellipsoid method actually consumes — but full-dimensionality is a consequence of the stated inequality, not a separate assertion.
--
--   **Scope.** The four claims are exactly the hypotheses that the ellipsoid iteration requires, and they are the only place where integrality of the data is used; the constants are one admissible choice, and any other choice of the same polynomial order supports the same downstream conclusion.
-- source:
--   L.G. Khachiyan, Soviet Math. Doklady 20 (1979) 191-194; quantification per B. Korte, J. Vygen, Combinatorial Optimization, 6th ed., Sections 4.4-4.5 (esp. the perturbation and volume lemmas), and Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Section 8.4.

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_SmaleNinth_Khachiyan

/-!
The quantitative heart of Khachiyan's theorem: the perturbed-and-boxed
system is feasibility-equivalent to the original integer system, bounded,
contained in an explicit ball, and — when nonempty — of explicitly
bounded-below volume.

Source: L.G. Khachiyan, *A polynomial algorithm in linear programming*,
Soviet Math. Doklady 20 (1979) 191–194; textbook quantification per
B. Korte, J. Vygen, *Combinatorial Optimization*, 6th ed., §4.4–4.5 and
Bertsimas–Tsitsiklis, *Introduction to Linear Optimization*, §8.4 (Lemmas
on full-dimensionality and volume of the perturbed system). The four
claims:

1. `Ax ≥ b` is solvable iff the perturbed-and-boxed system
   `Ax ≥ b − ε𝟙, −M𝟙 ≤ x ≤ M𝟙` is (Farkas with a Cramer-bounded dual
   certificate for one direction, the solution-size bound for the other);
2. the perturbed-and-boxed polyhedron is bounded;
3. it is contained in the ball `E(0, r²I)` with `r = (n+1)M`;
4. when nonempty, its volume is at least `v = (ε/(nU))ⁿ` (it contains a
   cube of side `ε/(nU)` around a solution of sup-norm `≤ M − 1`), so it is
   full-dimensional.

The constants `ε = khachiyanEps n U`, `M = khachiyanBox n U`,
`v = khachiyanVolLB n U`, `r = khachiyanRadius n U` are fixed in
`Definitions.Def_SmaleNinth_Khachiyan`.
-/

open Matrix LinearOptimization

/-- **Khachiyan's perturbation bounds** (Khachiyan 1979; Korte–Vygen
§4.4–4.5; Bertsimas–Tsitsiklis §8.4). For an integer system `Ax ≥ b` in
`n ≥ 1` variables with entries bounded by `U ≥ 1`, the perturbed-and-boxed
system `khachiyanSystemA A · x ≥ khachiyanSystemb n U b` is solvable iff
the original one is; it is bounded and contained in the ball of radius
`khachiyanRadius n U`; and when solvable its solution set has volume at
least `khachiyanVolLB n U` — in particular it is full-dimensional. -/

theorem SmaleNinth.khachiyan_perturbation_bounds {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    ((polyhedron (A.map (Int.cast : ℤ → ℝ))
        (fun i => (b i : ℝ))).Nonempty ↔
      (polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b)).Nonempty) ∧
    IsBoundedSet (polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b)) ∧
    polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b) ⊆
      ellipsoidBall 0 (khachiyanRadius n U) ∧
    ((polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b)).Nonempty →
      ENNReal.ofReal (khachiyanVolLB n U) ≤
        MeasureTheory.volume
          (polyhedron (khachiyanSystemA A) (khachiyanSystemb n U b))) := by sorry
