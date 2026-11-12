-- Prove2me | Theorems.Thm_ParallelLpSCO_EpochDA_lemma_22
-- name    : ParallelLpSCO.EpochDA.lemma_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:05:09.848979+00:00
-- url     : https://prove2.me/theorems/493afd32-8d67-4dfb-a6ae-356c24764efa
-- title:
--   Lemma 22 — p-MorGradEst has bias at most $C_p\lambda r^{p-1}/\sqrt{2^{j_{\max}}T_0}$ and $q$-th central moment at most $C_p\lambda^qr^pT_0^{-q/2}(1+\sum_j2^{-j(1-q/2)})$
-- statement:
--   Let $F:X\to\mathbb R$ satisfy Assumption 1, $y\in X$, $\lambda,r>0$, and
--   $$x^\star\in\operatorname*{argmin}_{x\in X}\Big\{F(x)+\frac\lambda p\|x-y\|_p^p\Big\},\qquad g=\lambda J_p(y-x^\star),$$
--   with $\|x^\star-y\|_p\le r$. Let $\hat g$ be the estimator of Algorithm 8 with $\delta_j=r/(2^jT_0)^{1/p}$, $0\le j\le j_{\max}$. Then, for a constant $C_p>0$ depending only on $p$,
--   $$\|\mathbb E\hat g-g\|_q\le\frac{C_p\lambda r^{p-1}}{\sqrt{2^{j_{\max}}T_0}},\qquad(44)$$
--   $$\mathbb E\|\hat g-\mathbb E\hat g\|_q^q\le\frac{C_p\lambda^qr^p}{T_0^{q/2}}\Big(1+\sum_{j=1}^{j_{\max}}2^{-j(1-q/2)}\Big).\qquad(45)$$
--
--   The multilevel estimator removes the bias of a single inexact proximal step at logarithmic cost. It is the stochastic proximal oracle of ball acceleration.
--
--   **Formalization Note.** The BROO is any mapping $O$ with Definition 5's guarantee for $F$ on $X$ with radius $r$; $J\sim\mathrm{Geom}(1/2)$ on $\{1,2,\dots\}$ (`geomHalf`). The $q$-th central moment is a lower Lebesgue integral. The constant $C$ is fixed before $d$, $F$, $X$, $y$, $\lambda$, $r$, the BROO, $T_0$ and $j_{\max}$.
--
--   Differences from the source:
--   - generalization: 'run with these values of T_0 and j_max' (Algorithm 8 line 2: T_0 = max{1, C_pλ^p r^{p(p−1)} log^{p−1}(2T_max)/σ^p}, j_max = ⌊log₂ T_max⌋) → every real T_0 ≥ 1 and every j_max ∈ ℕ; reason: the printed values satisfy T_0 ≥ 1, j_max ∈ ℕ, so the Lean statement specializes to them; Proposition 11 applies the lemma with other values (j_max = ⌈log₂ K⌉, T_0 = C_ba^{4p} log^{2p}(Rκ/r))
--   - encoding: an r-BROO O_{λ,δ}(·) (Definition 5) → any mapping O : λ ↦ δ ↦ y ↦ point satisfying IsBROO for F on X with radius r (min over X ∩ B_p(y, r)); reason: F is defined on X, so the ball minimum is over X ∩ B_p(y, r)
--   - encoding: E over J ∼ Geom(1/2) → integrals against geomHalf (P(J = j) = 2^{−j}, j ≥ 1); the central moment as a lower Lebesgue integral; reason: Geom(a) is on {1, 2, …} (p. 5); the estimator takes finitely many values
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), pp. 51–52, Lemma 22

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics
import Definitions.Def_ParallelLpSCO_EpochDA_Algorithms

open MeasureTheory

namespace ParallelLpSCO.EpochDA

/-- Lemma 22 (pp. 51–52). There is `C > 0` depending only on `p` such that, for `F` satisfying
Assumption 1 on `X`, `y ∈ X`, `λ, r > 0`, `x⋆ ∈ argmin_{x ∈ X} {F(x) + (λ/p)‖x − y‖_p^p}` with
`‖x⋆ − y‖_p ≤ r` and `g = λ J_p(y − x⋆)`, the estimator `ĝ` of Algorithm 8 (any `r`-BROO,
`J ∼ Geom(1/2)`, `δ_j = r/(2^j T₀)^{1/p}`) satisfies, for every `T₀ ≥ 1` and `j_max`,
`‖Eĝ − g‖_q ≤ C λ r^{p−1} / √(2^{j_max} T₀)` and
`E‖ĝ − Eĝ‖_q^q ≤ (C λ^q r^p / T₀^{q/2}) (1 + ∑_{j=1}^{j_max} 2^{−j(1−q/2)})`. -/
theorem lemma_22 (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (F : Vec d → ℝ) (X : Set (Vec d)), Assumption1 p F X →
      ∀ y : Vec d, y ∈ X → ∀ (lam r : ℝ), 0 < lam → 0 < r →
      ∀ xstar : Vec d, xstar ∈ X →
        (∀ x ∈ X, F xstar + lam / p * lpNorm p (xstar - y) ^ p ≤
          F x + lam / p * lpNorm p (x - y) ^ p) →
        lpNorm p (xstar - y) ≤ r →
      ∀ O : ℝ → ℝ → Vec d → Vec d, IsBROO p F X r O →
      ∀ T0 : ℝ, 1 ≤ T0 → ∀ jmax : ℕ,
        let q := conjExp p
        let gstar : Vec d := lam • Jp p (y - xstar)
        let ghat : ℕ → Vec d := morGradEst p r lam T0 jmax O y
        let Eg : Vec d := ∫ J, ghat J ∂geomHalf
        lpNorm q (Eg - gstar) ≤ C * lam * r ^ (p - 1) / Real.sqrt ((2 : ℝ) ^ jmax * T0) ∧
          ∫⁻ J, ENNReal.ofReal (lpNorm q (ghat J - Eg) ^ q) ∂geomHalf ≤
            ENNReal.ofReal (C * lam ^ q * r ^ p / T0 ^ (q / 2) *
              (1 + ∑ j ∈ Finset.Icc 1 jmax, (2 : ℝ) ^ (-(j : ℝ) * (1 - q / 2)))) := by sorry

end ParallelLpSCO.EpochDA
