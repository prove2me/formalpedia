-- Prove2me | Theorems.Thm_SemialgebraicSDP_Copositive_Supplement_theorem_7_5
-- name    : SemialgebraicSDP.Copositive.Supplement.theorem_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:42:39.881576+00:00
-- url     : https://prove2.me/theorems/f85261e5-46e4-4fc8-93e5-f6f81cab8f56
-- title:
--   Theorem 7.5, p. 316 — quadratic PSD multipliers making the quartic form (7.5) negative on ℝⁿ∖{0} show that the set $\mathcal A$ is empty
-- statement:
--   Let $A_1, \dots, A_m \in \mathcal S^n$ be real symmetric $n \times n$ matrices, write $A_i(x) := x^T A_i x$, and let
--   $$
--   \mathcal A := \{\, x \in \mathbb R^n \mid x^T A_i x \ge 0 \ (i = 1, \dots, m),\ \ \|x\| = 1 \,\}
--   $$
--   be the set (7.3), with $\|\cdot\|$ the Euclidean norm. Suppose there exist real symmetric positive semidefinite matrices $Q_1, \dots, Q_m \succeq 0$, with $Q_i(x) := x^T Q_i x$, and real numbers $r_{ij} \ge 0$ for $1 \le i < j \le m$, such that
--   $$
--   \sum_{i=1}^m Q_i(x) A_i(x) + \sum_{1 \le i < j \le m} r_{ij} A_i(x) A_j(x) < 0 \qquad \text{for all } x \in \mathbb R^n \setminus \{0\}. \tag{7.5}
--   $$
--   Then $\mathcal A = \emptyset$.
--
--   The classical certificate (7.4), $\sum_i \lambda_i A_i \preceq -I$ with $\lambda_i \ge 0$, is a Positivstellensatz refutation whose multipliers are constants. Theorem 7.5 allows quadratic multipliers and pairwise products of the constraints, which gives an infeasibility test at least as strong as (7.4): take $Q_i = \lambda_i I$ and $r_{ij} = 0$. The paper applies this test to MAX-CUT instances on which the standard relaxation has a gap.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, and the Euclidean unit sphere is written as $\sum_k x_k^2 = 1$ (Lean's default norm on this type is the sup norm). $A_i(x)$ and $Q_i(x)$ are the published quadratic evaluation `MurtyKabadi.Reduction.Q`. Symmetry of $A_i$ is `Matrix.IsSymm`, and $Q_i \in \mathcal S^n$, $Q_i \succeq 0$ is `Matrix.PosSemidef`, which over $\mathbb R$ includes symmetry. The $r_{ij}$ are entries of an array `Fin m → Fin m → ℝ`; only the entries with $i < j$ are constrained ($\ge 0$) and only they enter (7.5). The dimensions $n$ and $m$ are arbitrary, including $0$.
--
--   Differences from the source:
--   - encoding: $\|x\| = 1$ with the Euclidean norm → $\sum_k x_k^2 = 1$ on `Fin n → ℝ`; reason: same set, avoids Lean's sup norm on function types.
--   - encoding: $r_{ij} \in \mathbb R$ for $1 \le i < j \le m$ → an array `r : Fin m → Fin m → ℝ` with $r_{ij} \ge 0$ required only for $i < j$; reason: the entries with $i \ge j$ do not occur in (7.5) or in the conclusion, so no instance changes.
--   - reading: $A_i(x)$, not defined on the page → $x^T A_i x$; reason: (7.3) defines the constraints through $x^T A_i x$, and the paragraph after the proof calls the left side of (7.5) a homogeneous form of degree four.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 316, Theorem 7.5

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_SemialgebraicSDP_Copositive_Supplement_QuadraticSet

namespace SemialgebraicSDP.Copositive.Supplement

open MurtyKabadi.Reduction

/-- Theorem 7.5 (Parrilo 2003, p. 316). Let `A₁, …, Aₘ` be real symmetric `n × n` matrices.
Assume there exist real symmetric positive semidefinite `Qᵢ` and real `rᵢⱼ ≥ 0` (`i < j`) such
that `∑ᵢ Qᵢ(x)Aᵢ(x) + ∑_{i<j} rᵢⱼ Aᵢ(x)Aⱼ(x) < 0` for every nonzero `x ∈ ℝⁿ` (7.5). Then the
set `𝒜` of (7.3) is empty. -/
theorem theorem_7_5 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsSymm)
    (Qm : Fin m → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i, (Qm i).PosSemidef)
    (r : Fin m → Fin m → ℝ) (hr : ∀ i j, i < j → 0 ≤ r i j)
    (h75 : ∀ x : Fin n → ℝ, x ≠ 0 → quarticLHS A Qm r x < 0) :
    setA A = ∅ := by sorry

end SemialgebraicSDP.Copositive.Supplement
