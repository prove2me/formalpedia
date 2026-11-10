-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_lemma_4_5
-- name    : RandTensorIso.Smoothed.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:37:14.409202+00:00
-- url     : https://prove2.me/theorems/4868b792-d974-4aa1-b496-a21c1dd759de
-- title:
--   Lemma 4.5 — small-ball bound for non-clustered vectors [NV11, Corollary 2.10]
-- statement:
--   Let $\xi$ be a mean-zero, variance-one sub-Gaussian distribution, let $X\in\mathbb R^n$ have i.i.d. entries $X_i\sim\xi$, let $r>0$ and $q\ge1$, and let $z\in\mathbb R^n$ be a vector that is not $(q,r)$-clustered. Then there is $C>0$, depending only on $K_\xi$, such that for sufficiently large $n$,
--   $$\mathcal L(\langle z,X\rangle,r)\le\frac{C}{q\sqrt n}.$$
--   This is the inverse Littlewood–Offord input of the repulsion theorem (§4.4 uses it for Rademacher signs). In Lean, $C$ and the threshold $N_0$ are chosen from $K$ and are valid for every real $\xi$ with $K_\xi=K$, every $n\ge N_0$, $r>0$, integer $q\ge1$ and non-clustered $z$.
--
--   Differences from the source:
--   - reading: there exists C > 0, depending only on K_ξ, such that for sufficiently large n → C and N₀ chosen from K before ξ, n, r, q, z; reason: the uniform reading: neither the constant nor the threshold depends on r, q or z
--   - encoding: q ≥ 1 (a number of intervals) → q : ℕ with q ≥ 1; reason: Definition 4.4 counts intervals
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 52 (PDF 54), Lemma 4.5

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_SubGaussian

open MeasureTheory

namespace RandTensorIso.Smoothed

/-- Lemma 4.5 (p. 52, [NV11, Corollary 2.10]). For every `K > 0` there are `C > 0` (depending only
on `K_ξ = K`) and `N₀` such that for every mean-zero, variance-one sub-Gaussian `ξ` on `ℝ` with
`K_ξ = K`, every `n ≥ N₀`, every `r > 0`, every integer `q ≥ 1` and every `z ∈ ℝ^n` that is not
`(q, r)`-clustered, `L(⟨z, X⟩, r) ≤ C/(q√n)` for `X ∈ ℝ^n` with i.i.d. `ξ` entries. -/
theorem lemma_4_5 (K : ℝ) :
    ∃ (C : ℝ) (N₀ : ℕ), 0 < C ∧ ∀ (ξ : ProbabilityMeasure ℝ), IsStdSubGaussian (ξ : Measure ℝ) →
      subGaussConst (ξ : Measure ℝ) = K →
      ∀ (n : ℕ), N₀ ≤ n → ∀ (r : ℝ), 0 < r → ∀ (q : ℕ), 1 ≤ q →
      ∀ (z : Fin n → ℝ), ¬ IsClustered q r z →
        levyConc (vectorLawR ξ n) (fun X => ∑ i, z i * X i) r ≤
          ENNReal.ofReal (C / (q * Real.sqrt n)) := by sorry

end RandTensorIso.Smoothed
