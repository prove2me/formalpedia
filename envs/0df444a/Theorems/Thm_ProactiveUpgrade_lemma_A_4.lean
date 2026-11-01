-- Prove2me | Theorems.Thm_ProactiveUpgrade_lemma_A_4
-- name    : ProactiveUpgrade.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:19.157392+00:00
-- url     : https://prove2.me/theorems/465f0c01-f26d-4d4f-9f05-7d5b81d9bc4a
-- title:
--   Lemma A.4 — signs of the second differences of an anti-multimodular function
-- statement:
--   If $f$ is anti-multimodular with respect to $\mathcal F$, then
--
--   1. $\Delta_{e_i}\Delta_{e_j}f\le0$ for all $i,j$;
--   2. $\Delta_{e_i}\Delta_{e_i}f\le\Delta_{e_j}\Delta_{e_i}f$ for all $i,j$;
--   3. $\Delta_{e_i}\Delta_{d_i}f\ge0$ for $i\ne1$;
--   4. $\Delta_{d_i}\Delta_{d_i}f\le0$ for $i\ne1$;
--   5. $\Delta_{e_i}\Delta_{d_j}f\le0$ if $i<j$, $j\ne1$, and $\Delta_{e_i}\Delta_{d_j}f\ge0$ if $i>j$, $j\ne1$.
--
--   Each inequality holds at every point at which it evaluates $f$ only on $\mathbb N^n$. In particular an anti-multimodular function is submodular and concave in each coordinate.
--
--   Differences from the source:
--   - reading: Lemma A.4 for f : ℤᵐ → ℝ, inequalities everywhere on ℤᵐ → f on ℕⁿ; each inequality at every x whose evaluation points lie in ℕⁿ (both sides' points in (2)); reason: the quadrant reading of Definition A.1 (see AntiMultimodular)
--   - encoding: indices 1, …, m with i ≠ 1 → Fin n, 0-based, i ≠ 1 as 0 < i.val; reason: Lean convention
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Lemma A.4, p.31

import Mathlib
import Definitions.Def_ProactiveUpgrade_Dir
import Definitions.Def_ProactiveUpgrade_AntiMultimodular

namespace ProactiveUpgrade

/-- **Lemma A.4** (Chen et al., SSRN 3777846, p.31; proof pp.33–34). If `f` is anti-multimodular
with respect to `𝓕`, then
* (a) `∆_{eᵢ}∆_{eⱼ} f ≤ 0` for all `i, j`;
* (b) `∆_{eᵢ}∆_{eᵢ} f ≤ ∆_{eⱼ}∆_{eᵢ} f` for all `i, j`;
* (c) `∆_{eᵢ}∆_{dᵢ} f ≥ 0` for `i ≠ 1`;
* (d) `∆_{dᵢ}∆_{dᵢ} f ≤ 0` for `i ≠ 1`;
* (e) `∆_{eᵢ}∆_{dⱼ} f ≤ 0` if `i < j, j ≠ 1`, and `∆_{eᵢ}∆_{dⱼ} f ≥ 0` if `i > j, j ≠ 1`.

**Formalization Note** On the quadrant: each inequality is asserted at every `x` at which all the
points it evaluates lie in `ℕⁿ`. Indices are 0-based, so `i ≠ 1` reads `0 < i.val`. -/
theorem lemma_A_4 {n : ℕ} (f : (Fin n → ℕ) → ℝ) (hf : AntiMultimodular f) :
    (∀ (i j : Fin n) (x : Fin n → ℤ), EvalInQuad (Dir.posE i) (Dir.posE j) x →
      (Dir.posE i).delta ((Dir.posE j).delta (liftZ f)) x ≤ 0) ∧
    (∀ (i j : Fin n) (x : Fin n → ℤ), EvalInQuad (Dir.posE i) (Dir.posE i) x →
      EvalInQuad (Dir.posE j) (Dir.posE i) x →
      (Dir.posE i).delta ((Dir.posE i).delta (liftZ f)) x ≤
        (Dir.posE j).delta ((Dir.posE i).delta (liftZ f)) x) ∧
    (∀ (i : Fin n) (hi : 0 < i.val) (x : Fin n → ℤ), EvalInQuad (Dir.posE i) (Dir.dd i hi) x →
      0 ≤ (Dir.posE i).delta ((Dir.dd i hi).delta (liftZ f)) x) ∧
    (∀ (i : Fin n) (hi : 0 < i.val) (x : Fin n → ℤ), EvalInQuad (Dir.dd i hi) (Dir.dd i hi) x →
      (Dir.dd i hi).delta ((Dir.dd i hi).delta (liftZ f)) x ≤ 0) ∧
    (∀ (i j : Fin n) (hj : 0 < j.val) (x : Fin n → ℤ), EvalInQuad (Dir.posE i) (Dir.dd j hj) x →
      (i < j → (Dir.posE i).delta ((Dir.dd j hj).delta (liftZ f)) x ≤ 0) ∧
      (j < i → 0 ≤ (Dir.posE i).delta ((Dir.dd j hj).delta (liftZ f)) x)) := by sorry

end ProactiveUpgrade
