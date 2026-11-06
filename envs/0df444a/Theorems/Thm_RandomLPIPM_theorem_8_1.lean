-- Prove2me | Theorems.Thm_RandomLPIPM_theorem_8_1
-- name    : RandomLPIPM.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:27.721514+00:00
-- url     : https://prove2.me/theorems/d65838a1-f0c1-44b3-832b-a1383c90870c
-- title:
--   Theorem 8.1 — two-sided bounds on the positive optimal coordinates of LP(A)
-- statement:
--   Let $A\in\mathbb R^{d\times n}$ have independent $\mathcal N(0,1)$ entries, $1\le d<n$, $n\ge2$, and let $(x^*,s^*)$ be the optimal solution of LP(A), $B^*=\operatorname{supp}(x^*)$, $N^*=\operatorname{supp}(s^*)$,
--   $$m^*=\min\Big\{\min_{i\in B^*}x^*_i,\ \min_{j\in N^*}s^*_j\Big\},\qquad M^*=\max\{\|x^*\|_\infty,\|s^*\|_\infty\}.$$
--   Then
--   1. $M^*\le n$ (deterministically);
--   2. for every $u>0$, $\Pr(m^*\le u)\le\min\{1,16n^2u\}$;
--   3. for every $q>0$, with probability at least $1-n^{-q}$, every positive coordinate of $(x^*,s^*)$ lies in $\big[n^{-(q+2)}/16,\ n\big]$.
--
--   These bounds are what make basis identification from an approximate central point possible at $\mu=1/\operatorname{poly}(n)$.
--
--   Differences from the source:
--   - generalization: M* ≤ n for the optimal solution of LP(A) with Gaussian A → x_i ≤ n and s_i ≤ n for every matrix A and every optimal (x, y, s) of LP(A); reason: the bound is deterministic (Lemma 8.10); the source's case is an instance
--   - generalization: Pr(m* ≤ u) and the event of clause 3 for the (almost surely unique) optimal solution → the events that some optimal (x, y, s) has a positive coordinate ≤ u, resp. outside [n^(−(q+2))/16, n]; reason: these events contain the source's events, so the bounds imply the printed ones
--   - encoding: probability of the event → outer Gaussian measure of the failure set bounded by the failure probability; reason: no measurability assumption is needed; for a measurable event it is 1 − P(event)
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 8.1, p.68

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_IsPDOptimal

open Matrix MeasureTheory

namespace RandomLPIPM

/-- **Theorem 8.1 (Two-sided optimal-coordinate bounds).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 8.1, p.68.

Section 8 setting (p.68): `A ∈ ℝ^{d×n}` with independent `N(0,1)` entries, `1 ≤ d < n`. Let `n ≥ 2`,
`(x*, s*)` the optimal solution of LP(A), `B* = supp(x*)`, `N* = supp(s*)`,
`m* = min{min_{B*} x*ᵢ, min_{N*} s*ⱼ}` the minimum positive optimal coordinate and
`M* = max{‖x*‖_∞, ‖s*‖_∞}`. Then (i) `M* ≤ n`; (ii) for `u > 0`, `Pr(m* ≤ u) ≤ min{1, 16n²u}`;
(iii) for every `q > 0`, with probability at least `1 − n^{−q}`, every positive coordinate of
`(x*, s*)` lies in `[n^{−(q+2)}/16, n]`.

**Formalization Note.** (i) is stated for every `A` and every optimal solution (it is deterministic,
Lemma 8.10). In (ii) and (iii) the failure events are taken over *every* optimal solution
`(x, y, s)` of LP(A): "`m* ≤ u`" becomes "some optimal solution has a positive coordinate `≤ u`".
The optimum is almost surely unique (Corollary 8.4), so this is the paper's event up to a null set,
and it contains the paper's event. -/
theorem theorem_8_1 (d n : ℕ) (hn : 2 ≤ n) (hd1 : 1 ≤ d) (hdn : d < n) :
    (∀ (A : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ) (y : Fin d → ℝ) (s : Fin n → ℝ),
      IsPDOptimal A (A *ᵥ 1) 1 x y s → ∀ i, x i ≤ n ∧ s i ≤ n) ∧
    (∀ u : ℝ, 0 < u →
      GaussianMatrix.gaussianMatrix d n {A | ∃ (x : Fin n → ℝ) (y : Fin d → ℝ) (s : Fin n → ℝ),
          IsPDOptimal (Matrix.of A) (Matrix.of A *ᵥ 1) 1 x y s ∧
          ∃ i, (0 < x i ∧ x i ≤ u) ∨ (0 < s i ∧ s i ≤ u)} ≤
        ENNReal.ofReal (min 1 (16 * (n : ℝ) ^ 2 * u))) ∧
    (∀ q : ℝ, 0 < q →
      GaussianMatrix.gaussianMatrix d n {A | ∃ (x : Fin n → ℝ) (y : Fin d → ℝ) (s : Fin n → ℝ),
          IsPDOptimal (Matrix.of A) (Matrix.of A *ᵥ 1) 1 x y s ∧
          ∃ i, (0 < x i ∧ ¬ ((n : ℝ) ^ (-(q + 2)) / 16 ≤ x i ∧ x i ≤ n)) ∨
               (0 < s i ∧ ¬ ((n : ℝ) ^ (-(q + 2)) / 16 ≤ s i ∧ s i ≤ n))} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-q))) := by sorry

end RandomLPIPM
