-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_lemma_4_2
-- name    : PoissonDepTrials.MixInv.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:05:10.782913+00:00
-- url     : https://prove2.me/theorems/f4d4ac57-9698-482e-839c-e605b84383ca
-- title:
--   Lemma 4.2, p. 539 — |E^Y f(Y, Z) − E^Y f(Y, Z′)| ≤ 2‖f‖φ(m) for Y ∈ ℳ_{1k}, Z ∈ ℳ_{k+m,∞}
-- statement:
--   Let $X_1,X_2,\dots$ be an arbitrary sequence of real random variables satisfying the mixing condition (4.1) with coefficients $\varphi$. Let $Y=(Y_1,\dots,Y_r)$ be measurable with respect to $\mathcal M_{1k}$ and $Z=(Z_1,\dots,Z_s)$ measurable with respect to $\mathcal M_{k+m,\infty}$, $m\ge1$. Then for every bounded Borel function $f:\mathbb R^{r+s}\to\mathbb R$,
--   $$|E^Yf(Y,Z)-E^Yf(Y,Z')|\le2\|f\|\varphi(m)\quad\text{a.s.},$$
--   where $Z'$ has the law of $Z$ and is independent of the sequence. It is the decoupling inequality used in Lemmas 4.3 and 4.4.
--
--   **Formalization Note** The sequence is real valued and measurable (needed for $\mathcal M_{a,b}$ to be a sub-$\sigma$-algebra). $\mathbb R^{r+s}$ is written $\mathbb R^r\times\mathbb R^s$. $E^Yf(Y,Z')$ is written, almost surely, as $\int f(Y,z)\,P_Z(dz)$, which avoids enlarging $\Omega$ to carry $Z'$. $\|f\|$ is a bound $M$; the lag satisfies $m\ge1$, as in (4.1).
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 539, Lemma 4.2, (4.4)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (r s k m : ℕ) (hm : 1 ≤ m)
    (Y : Ω → (Fin r → ℝ)) (hY : Measurable[sigmaIcc X 1 k] Y)
    (Z : Ω → (Fin s → ℝ)) (hZ : Measurable[sigmaIci X (k + m)] Z)
    (f : (Fin r → ℝ) × (Fin s → ℝ) → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    ∀ᵐ ω ∂P, |(P[fun ω => f (Y ω, Z ω) | MeasurableSpace.comap Y inferInstance]) ω
      - ∫ z, f (Y ω, z) ∂(P.map Z)| ≤ 2 * M * φ m := by sorry

end PoissonDepTrials.MixInv
