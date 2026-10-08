-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_theorem_2_10
-- name    : SkutellaCQP.NoRel.theorem_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:24.190547+00:00
-- url     : https://prove2.me/theorems/c3c07956-322c-4da4-ace8-e806413d69a6
-- title:
--   Theorem 2.10, p. 14 — integral data and Z < Z*_CQP′ + 1/3: some outcome of rounding is a 3/2-approximate schedule
-- statement:
--   Suppose all weights $w_j$ and processing times $p_{ij}$ are integers. Let $(\bar a,Z)$ be feasible for (CQP′) and near optimal, $Z<Z^*_{CQP'}+\tfrac13$, i.e. $Z<Z'+\tfrac13$ for every feasible $(a',Z')$ of (CQP′). Then there is an assignment $\sigma$ that sends every job $j$ to a machine $i$ with $\bar a_{ij}>0$ — a possible outcome of rounding $\bar a$, as produced by Algorithm DERANDOMIZED ROUNDING — whose value is within $3/2$ of the optimum:
--
--   $$
--   \sum_jw_jC_j(\sigma)\le\tfrac32\cdot\sum_jw_jC_j(\tau)\qquad\text{for every assignment }\tau .
--   $$
--
--   This is the integrality argument that turns the bound $\tfrac32Z^*+\tfrac12$ into the $3/2$-approximation of Theorem 2.10.
--
--   **Formalization Note** The paper's theorem is about an algorithm (computing a near-optimal solution of (CQP′) within additive error and derandomizing by conditional probabilities, in polynomial time). Neither the running time nor the specific derandomization procedure is formalized; the statement asserts the existence of an outcome in the support of the rounding with the guarantee. The support condition makes it non-trivial: an optimal schedule need not lie in the support of $\bar a$. The standing assumptions $p_{ij}>0$, $w_j\ge0$ are hypotheses; integrality is the page's hypothesis "all weights and processing times are integral".
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 14, Theorem 2.10 and its proof

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

/-- The integrality step of Theorem 2.10 (p. 14). With integral weights and processing times, let
`(a, Z)` be feasible for (CQP′) with `Z < Z*_CQP′ + 1/3`. Then some assignment that sends every job
`j` to a machine `i` with `a_ij > 0` (a possible outcome of rounding `a`) has value at most `3/2`
times the value of every schedule. -/
theorem theorem_2_10 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (hpint : ∀ i j, ∃ z : ℤ, p i j = z) (hwint : ∀ j, ∃ z : ℤ, w j = z)
    (a : Fin m → Fin n → ℝ) (Z : ℝ) (haZ : CQP'Feasible p w a Z)
    (hnear : ∀ (b : Fin m → Fin n → ℝ) (Y : ℝ), CQP'Feasible p w b Y → Z < Y + 1 / 3) :
    ∃ σ : Fin n → Fin m, (∀ j, 0 < a (σ j) j) ∧
      ∀ τ : Fin n → Fin m, val p w σ ≤ (3 / 2) * val p w τ := by sorry

end SkutellaCQP.NoRel
