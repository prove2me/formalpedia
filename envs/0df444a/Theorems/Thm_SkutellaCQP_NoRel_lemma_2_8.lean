-- Prove2me | Theorems.Thm_SkutellaCQP_NoRel_lemma_2_8
-- name    : SkutellaCQP.NoRel.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:13.611044+00:00
-- url     : https://prove2.me/theorems/dba7aed6-e582-414c-9e28-2f97ed1c18f0
-- title:
--   Lemma 2.8, p. 14 — rounding any (CQP′)-feasible (ā, Z) gives expected value ≤ 3/2 · Z
-- statement:
--   Let $(\bar a,Z)$ be a feasible solution of (CQP′): $\sum_i\bar a_{ij}=1$ for every $j$, $\bar a\ge 0$, $Z\ge\tfrac12c^T\bar a+\tfrac12\bar a^T(D+\operatorname{diag}(c))\bar a$ (12) and $Z\ge c^T\bar a$ (13). Then Algorithm RANDOMIZED ROUNDING applied to $\bar a$ (pairwise independent choices, Smith sequencing) computes a schedule with
--
--   $$
--   \mathbb E\Bigl[\sum_jw_jC_j\Bigr]\le\tfrac32\cdot Z .
--   $$
--
--   Together with the fact that every schedule is feasible for (CQP′), this gives the $3/2$ guarantee of §2.4.
--
--   **Formalization Note** $Z$ plays the role of $Z_{CQP'}(\bar a)$, the value of the feasible solution. The standing assumptions $p_{ij}>0$, $w_j\ge 0$ are hypotheses.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 14, Lemma 2.8

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.NoRel

/-- Lemma 2.8 (p. 14). For any feasible solution `(a, Z)` of (CQP′), randomized rounding with
pairwise independent choices yields a schedule of expected value at most `3/2 · Z`. -/
theorem lemma_2_8 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (a : Fin m → Fin n → ℝ) (Z : ℝ) (haZ : CQP'Feasible p w a Z)
    (μ : (Fin n → Fin m) → ℝ) (hμ : IsPairwiseRounding a μ) :
    E μ (val p w) ≤ (3 / 2) * Z := by sorry

end SkutellaCQP.NoRel
