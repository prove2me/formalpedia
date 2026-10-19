-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapO14_convexSubgradient_quantum
-- name    : QAlgorithms.Papers.RoadmapO14.convexSubgradient_quantum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:29:38.16891+00:00
-- url     : https://prove2.me/theorems/1ffd6bd0-d4ef-4f25-9a06-826941dc9f5e
-- title:
--   Lemma 18: approximate convex subgradient from logarithmically many quantum value queries
-- statement:
--   Let $n\ge1$, let $C\subseteq\mathbb R^n$ be convex, and let $f:C\to\mathbb R$ be convex. Assume $r_1,L>0$, $0<\rho\le1/3$, $0<\delta\le r_1nL/\rho$, and $B_\infty(0,2r_1)\subseteq C$. On this closed cube, assume that $f$ is $L$-Lipschitz in the Euclidean norm. Suppose finite binary quantum value-oracle access is available on a sufficiently fine hypergrid of this cube: the standard unitary preserves the query index and adds a fixed-point value within $\delta$ of $f$. Its inverse is also available.
--
--   There is a quantum algorithm, fixed from the known parameters, grid and encoding before the unknown function and oracle, whose output $\widetilde g\in\mathbb R^n$ satisfies, with probability at least $1-\rho$, simultaneously for every $y\in C$,
--   $$
--   \begin{aligned}
--   f(y)&\ge f(0)+\langle\widetilde g,y\rangle
--   -23^2\sqrt{\frac{\delta n^3L}{\rho r_1}}\,\|y\|_1-2L\sqrt n\,r_1,\\
--   f(y)&\ge f(0)+\langle\widetilde g,y\rangle
--   -(23n)^2\sqrt{\frac{\delta L}{\rho r_1}}\,\|y\|_2-2L\sqrt n\,r_1.
--   \end{aligned}
--   $$
--   The total number of forward and inverse oracle calls is $O(\log(n/\rho))$, with an absolute constant uniform over all parameters, domains, functions, encodings, precision and oracle implementations. Precisely, there are absolute $K>0$ and $s_0\ge1$ such that this count is at most $\lceil K\log(n/\rho)\rceil$ when $n/\rho\ge s_0$; a successful finite algorithm exists throughout the admissible parameter range.
--
--   The same conclusion and query bound hold for a relational unitary $\delta$-approximator: on each clean query input it preserves the input and yields a value within $\delta$ with probability at least $2/3$, with arbitrary normalized conditional garbage. Access to its inverse is allowed.
--
--   This result supplies a uniformly valid approximate supporting hyperplane without assuming differentiability or a smoothness bound on the objective.
--
--   **Formalization Note** The sufficiently fine access condition is explicit geometric coverage of compatible finite-difference and uniform-center grids and translated/scaled Definition-13 midpoint grids. An existential positive resolution threshold allows arbitrarily small mesh and radius-rounding budgets. Known-parameter arithmetic guards preserve the printed constants; neither local near-linearity nor small curvature is an input hypothesis. Grid indices remain exact finite labels under their known affine embedding. The real extension of $f$ outside $C$ is immaterial. No gate bound or convex-set oracle reduction is asserted.
-- source:
--   Convex optimization using quantum oracles, arXiv:1809.00643v4, §3.2, Lemma 18 (proof p.13; footnote 7), PDF p. 12. https://arxiv.org/abs/1809.00643v4 . PDF SHA-256: 0eb94a52d9ef09d903beb9638bf07a5c37a55141043d8c4dac043db8cde92da0.

import Definitions.Def_QAlgorithms_Defs_GridSubgradientPrograms
import Definitions.Def_QAlgorithms_Papers_RoadmapO14_Model
set_option autoImplicit false

noncomputable section

namespace QAlgorithms.Papers.RoadmapO14

open QAlgorithms.ValueAccess

/-- Lemma 18, arXiv:1809.00643v4, PDF p.12, proof p.13, including the relational
extension in footnote 7 (Definitions 2 and 28, pp.5 and 27).
Absolute asymptotic constants precede all instances. Resolution is geometric and can be
arbitrarily fine. Each actual procedure, normalized starts, workspace, input-independent
unitaries and decoder is fixed before C, f, the answer table and U. All uncontrolled U
and adjoint calls count; input is a value oracle. The conjuncts are the standard and
relational versions of this one headline result. -/
theorem convexSubgradient_quantum :
    ∃ K : ℝ, 0 < K ∧ ∃ scale0 : ℝ, 1 ≤ scale0 ∧
    ∀ n : ℕ, 1 ≤ n → ∀ r1 L delta rho : ℝ,
    0 < r1 → 0 < L → 0 < rho → rho ≤ 1 / 3 →
    0 < delta → delta ≤ r1 * n * L / rho →
    ∃ resolution : ℝ, 0 < resolution ∧
      (∀ precision : ℝ, 0 < precision → precision ≤ resolution →
        ∃ H : SubgradientGrid n, HasSubgradientGeometry H r1 L delta rho precision) ∧
      ∀ precision : ℝ, 0 < precision → precision ≤ resolution →
      ∀ H : SubgradientGrid n, HasSubgradientGeometry H r1 L delta rho precision →
        (∀ b : ℕ, ∀ encoding : FixedPointEncoding b,
          ∃ work : ℕ, ∃ P : RandomizedQueryProcedure n (GridIndex H × Qubits b) (Fin work),
            (scale0 ≤ (n : ℝ) / rho →
              procedureQueries P ≤ ⌈K * Real.log ((n : ℝ) / rho)⌉₊) ∧
            ∀ (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
              IsLemma18Function C f r1 L →
              ∀ U : Matrix (GridIndex H × Qubits b) (GridIndex H × Qubits b) ℂ,
                IsApproxBinaryValueOracle (queryPoint H) encoding.value false f delta U →
                queryProcedureLaw P U (SubgradientEvent C f r1 L delta rho) ≥ 1 - rho) ∧
        (∀ b w : ℕ, ∀ encoding : FixedPointEncoding b,
          ∃ work : ℕ,
          ∃ P : RandomizedQueryProcedure n (GridIndex H × (Qubits b × Qubits w)) (Fin work),
            (scale0 ≤ (n : ℝ) / rho →
              procedureQueries P ≤ ⌈K * Real.log ((n : ℝ) / rho)⌉₊) ∧
            ∀ (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
              IsLemma18Function C f r1 L →
              ∀ U : Matrix (GridIndex H × (Qubits b × Qubits w))
                  (GridIndex H × (Qubits b × Qubits w)) ℂ,
                IsRelationalValueApproximator (queryPoint H) encoding.value f delta U →
                queryProcedureLaw P U (SubgradientEvent C f r1 L delta rho) ≥ 1 - rho) := by sorry

end QAlgorithms.Papers.RoadmapO14
