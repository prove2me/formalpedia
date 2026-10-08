-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_corollary_2_11
-- name    : SkutellaCQP.NoRel.corollary_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:42.623695+00:00
-- url     : https://prove2.me/theorems/8d34956b-90ca-4030-ad2b-8ab29e359aff
-- title:
--   Corollary 2.11, p. 14 — rounding a (CQP′)-feasible (ā, Z) gives expected value ≤ (1 + cᵀā/(2Z))·Z
-- statement:
--   For any feasible solution $(\bar a,Z)$ of (CQP′) with $Z>0$, Algorithm RANDOMIZED ROUNDING (pairwise independent choices, Smith sequencing) computes a feasible schedule with
--
--   $$
--   \mathbb E\Bigl[\sum_jw_jC_j\Bigr]\le\Bigl(1+\frac{c^T\bar a}{2Z}\Bigr)\cdot Z .
--   $$
--
--   Since $c^T\bar a\le Z$ by (13), this refines Lemma 2.8: the guarantee improves when $Z$ is much larger than $c^T\bar a$. It is used in §5 for two machines.
--
--   **Formalization Note** $Z$ stands for the page's $Z_{CQP'}(\bar a)$. The hypothesis $Z>0$ is added: the page's fraction $c^T\bar a/(2Z_{CQP'}(\bar a))$ presupposes it. The standing assumptions $p_{ij}>0$, $w_j\ge 0$ are hypotheses.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 14, Corollary 2.11

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

/-- Corollary 2.11 (p. 14). For any feasible solution `(a, Z)` of (CQP′) with `Z > 0`, randomized
rounding with pairwise independent choices yields a schedule of expected value at most
`(1 + c^T a / (2 Z)) · Z`. -/
theorem corollary_2_11 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (a : Fin m → Fin n → ℝ) (Z : ℝ) (haZ : CQP'Feasible p w a Z) (hZ : 0 < Z)
    (μ : (Fin n → Fin m) → ℝ) (hμ : IsPairwiseRounding a μ) :
    E μ (val p w) ≤ (1 + (cvec p w ⬝ᵥ vec a) / (2 * Z)) * Z := by sorry

end SkutellaCQP.NoRel
