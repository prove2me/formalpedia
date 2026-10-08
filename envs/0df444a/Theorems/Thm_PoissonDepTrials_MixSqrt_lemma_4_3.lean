-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_4_3
-- name    : PoissonDepTrials.MixSqrt.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:06.627736+00:00
-- url     : https://prove2.me/theorems/7505e103-498e-4b4b-befa-f522c7f0237a
-- title:
--   Lemma 4.3, p. 539 — |Ef(Y, Z)g(T) − Ef(Y, Z)Eg(T)| ≤ 4φ(m)‖f‖E|g(T)| + 2φ(m)‖g‖E|f(Y, Z′)|
-- statement:
--   Let $X_1,X_2,\dots$ be an arbitrary sequence of real random variables satisfying (4.1) with $\varphi$, and let $m\ge1$. Let $Y,T,Z$ be real random variables measurable with respect to $\mathcal M_{ab}$, $\mathcal M_{cd}$, $\mathcal M_{ee'}$ respectively, where $a\ge1$, $c-b\ge m$ and $e-d\ge m$. Let $g:\mathbb R\to\mathbb R$ and $f:\mathbb R^2\to\mathbb R$ be Borel with $|g|\le\|g\|$ and $|f|\le\|f\|$. Then
--   $$\bigl|Ef(Y,Z)g(T)-Ef(Y,Z)\,Eg(T)\bigr|\le4\varphi(m)\|f\|\,E|g(T)|+2\varphi(m)\|g\|\,E|f(Y,Z')|,$$
--   where $Z'$ has the law of $Z$ and is independent of $X_1,X_2,\dots$, so that $E|f(Y,Z')|=\iint|f(y,z)|\,P_Y(dy)P_Z(dz)$.
--
--   This covariance inequality, for a middle block $T$ separated from an outer pair $(Y,Z)$, is what bounds the term $\sum_iE[(X_i-p_i)f(V^{(i)}+1)]$ in Lemma 4.6.
--
--   **Formalization Note** $\|f\|$ and $\|g\|$ are arbitrary bounds $M_f$, $M_g$. $E|f(Y,Z')|$ is written as the integral of $|f|$ against the product of the laws of $Y$ and $Z$. The page names the last index pair $e,f$; the upper index is renamed $e'$ to avoid a clash with the function $f$. $a\ge1$ because the sequence starts at $X_1$, and $m\ge1$ because (4.1) concerns lags $\ge1$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), pp. 539–540, Lemma 4.3, (4.5)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 4.3, p. 539, (4.5). Let `X_1, X_2, …` be a real sequence satisfying (4.1), and
`Y, T, Z` real random variables measurable `ℳ_{ab}, ℳ_{cd}, ℳ_{ee'}` with `c − b ≥ m`, `e − d ≥ m`.
For bounded Borel `g : ℝ → ℝ` and `f : ℝ² → ℝ`,
`|Ef(Y, Z)g(T) − Ef(Y, Z)Eg(T)| ≤ 4φ(m)‖f‖E|g(T)| + 2φ(m)‖g‖E|f(Y, Z')|`, where `Z'` is an independent
copy of `Z`, so `E|f(Y, Z')|` is the integral of `|f|` against the product of the laws of `Y`
and `Z`. -/
theorem lemma_4_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (m : ℕ) (hm : 1 ≤ m) (a b c d e e' : ℕ) (ha : 1 ≤ a) (hbc : b + m ≤ c) (hde : d + m ≤ e)
    (Y T Z : Ω → ℝ) (hY : Measurable[sigmaIcc X a b] Y) (hT : Measurable[sigmaIcc X c d] T)
    (hZ : Measurable[sigmaIcc X e e'] Z)
    (g : ℝ → ℝ) (hg : Measurable g) (Mg : ℝ) (hMg : ∀ x, |g x| ≤ Mg)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) (Mf : ℝ) (hMf : ∀ x, |f x| ≤ Mf) :
    |∫ ω, f (Y ω, Z ω) * g (T ω) ∂P - (∫ ω, f (Y ω, Z ω) ∂P) * ∫ ω, g (T ω) ∂P|
      ≤ 4 * φ m * Mf * ∫ ω, |g (T ω)| ∂P
        + 2 * φ m * Mg * ∫ x, |f x| ∂((P.map Y).prod (P.map Z)) := by sorry

end PoissonDepTrials.MixSqrt
