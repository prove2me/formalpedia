-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_A_4
-- name    : PrivGaussMS.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:54.503386+00:00
-- url     : https://prove2.me/theorems/2f012a92-1ac6-48c1-ad4b-3271ba764db1
-- title:
--   Lemma A.4 — Laplace noise and bounded (clipped) noise
-- statement:
--   Let $g$ be real valued with sensitivity at most $\Delta\ge0$ on neighbouring datasets, and let $Z\sim\mathrm{Lap}(b)$ with $b>0$ and density $e^{-|z|/b}/(2b)$. Then:
--
--   1. $g(x)+Z$ is $(\Delta/b,0)$-private;
--   2. $\mathbb P\{|Z|>\ell\}=e^{-\ell/b}$ for $\ell\ge0$;
--   3. for $\mathrm{clip}_\ell(z)=\max\{-\ell,\min\{z,\ell\}\}$ and $\ell\ge0$, $g(x)+\mathrm{clip}_\ell(Z)$ is $(\Delta/b,(1+e^{\Delta/b})e^{-\ell/b})$-private;
--   4. any fixed test applied to either release preserves its guarantee.
--
--   This is the clipped Laplace test inside the sampler.
--
--   Differences from the source:
--   - reading: 'any fixed test' → any Markov kernel from ℝ to Bool that does not see the input; reason: covers deterministic and randomized tests
--   - encoding: a randomized mechanism and its output law → a family of output laws, with IsDPM asserting that each is a probability measure and applying the published IsDP; reason: Lean pushes a non-measurable map to the zero measure, under which DP would hold vacuously; the assertion rules this out and changes no instance
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma A.4, p.25

import Mathlib
import Definitions.Def_PrivGaussMS_Basics

open MeasureTheory ProbabilityTheory PrivateUniformGen.Characterization

namespace PrivGaussMS

/-- **Lemma A.4** (Laplace noise and bounded noise), Moayedi, Yassaee, Ebrahimi, *Optimal Private
Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…), p.25.

Let `g` be real valued with sensitivity at most `Δ ≥ 0` on neighbouring datasets and
`Z ∼ Lap(b)`, `b > 0`, density `e^{−|z|/b}/(2b)`. Then `g(x) + Z` is `(Δ/b, 0)`-private;
`P{|Z| > ℓ} = e^{−ℓ/b}` for `ℓ ≥ 0`; `g(x) + clip_ℓ(Z)` is `(Δ/b, (1 + e^{Δ/b})e^{−ℓ/b})`-private;
and any fixed test applied to either release preserves its guarantee.

**Formalization Note.** A fixed test is any Markov kernel from `ℝ` to `{0, 1}` (`Bool`) that does
not see the input, deterministic tests included. Neighbours are the published replacement
neighbours. -/
theorem lemma_A_4 {X : Type*} {n : ℕ} (g : (Fin n → X) → ℝ) (Δ b : ℝ) (hΔ : 0 ≤ Δ)
    (hb : 0 < b) (hg : ∀ x x', Neighbors x x' → |g x - g x'| ≤ Δ) :
    IsDPM (fun x => (laplace b).map fun z => g x + z) (Δ / b) 0 ∧
    (∀ ℓ : ℝ, 0 ≤ ℓ → (laplace b).real {z | ℓ < |z|} = Real.exp (-ℓ / b)) ∧
    (∀ ℓ : ℝ, 0 ≤ ℓ → IsDPM (fun x => (laplace b).map fun z => g x + clip ℓ z) (Δ / b)
      ((1 + Real.exp (Δ / b)) * Real.exp (-ℓ / b))) ∧
    (∀ K : Kernel ℝ Bool, IsMarkovKernel K →
      IsDPM (fun x => ((laplace b).map fun z => g x + z).bind K) (Δ / b) 0 ∧
      ∀ ℓ : ℝ, 0 ≤ ℓ → IsDPM (fun x => ((laplace b).map fun z => g x + clip ℓ z).bind K)
        (Δ / b) ((1 + Real.exp (Δ / b)) * Real.exp (-ℓ / b))) := by sorry

end PrivGaussMS
