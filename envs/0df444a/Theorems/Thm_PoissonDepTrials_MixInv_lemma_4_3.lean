-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_lemma_4_3
-- name    : PoissonDepTrials.MixInv.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:05:30.636609+00:00
-- url     : https://prove2.me/theorems/a87dc991-d81f-4d74-a595-e196c2851763
-- title:
--   Lemma 4.3, p. 539 — |Ef(Y,Z)g(T) − Ef(Y,Z)Eg(T)| ≤ 4φ(m)‖f‖E|g(T)| + 2φ(m)‖g‖E|f(Y,Z′)|
-- statement:
--   Let $X_1,X_2,\dots$ be an arbitrary sequence of real random variables satisfying (4.1). Let $Y,T,Z$ be random variables measurable with respect to $\mathcal M_{ab}$, $\mathcal M_{cd}$, $\mathcal M_{ee'}$ respectively, where $c-b\ge m$ and $e-d\ge m$, and let $g:\mathbb R\to\mathbb R$ and $f:\mathbb R^2\to\mathbb R$ be bounded and Borel measurable. Then
--   $$|Ef(Y,Z)g(T)-Ef(Y,Z)\,Eg(T)|\le4\varphi(m)\|f\|E|g(T)|+2\varphi(m)\|g\|E|f(Y,Z')|,$$
--   where $Z'$ has the law of $Z$ and is independent of $X_1,X_2,\dots$. It bounds the covariance terms in Lemma 4.6 and in (4.17).
--
--   **Formalization Note** The page's index $f$ of $\mathcal M_{ef}$ clashes with the function $f$ and is renamed $e'$. $c-b\ge m$, $e-d\ge m$ are written $b+m\le c$, $d+m\le e$; $a\ge1$ and $m\ge1$ as in (4.1). $E|f(Y,Z')|$ is the integral of $|f|$ against the product of the laws of $Y$ and $Z$. Norms are bounds $M_f$, $M_g$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), pp. 539–540, Lemma 4.3, (4.5)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

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

end PoissonDepTrials.MixInv
