-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_equations_26_27
-- name    : RankingQueryCost.Joint.equations_26_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:28:24.596179+00:00
-- url     : https://prove2.me/theorems/8ecf206b-5a3a-4e84-9d4e-37a54005e4eb
-- title:
--   Equations (26)–(27) — Adaptive correction identity and sampling moment
-- statement:
--   Let $r,\pi$ be true and warm rank permutations, and $0<p\le1$. Use the computed correction, sampling noise and erroneous flow of §6.2. Conditional on the fixed warm history,
--
--   $$\widetilde q-r=Z+F_{\rm err},\qquad
--   \mathbb E\|Z\|_2^2=2(1/p-1)K(r,\pi).$$
--
--   Here $K$ is the unweighted Kendall inversion count, and the expectation is over independent Bernoulli inclusions. The vector identity holds coordinatewise and permits arbitrary observed inversion indicators. The statement also includes the source's unconditional bound $\mathbb E\|Z\|_2^2\le2K/p$: for any probability law on warm permutations whose mean Kendall count is at most $K$, average over that law and an independent Bernoulli mask. Lemma 6.1 supplies this premise for the constructed warm order. These are unnumbered equations, not an invented numbered milestone.
--
--   Differences from the source:
--   - encoding: expectation under fresh independent Bernoulli sampling conditional on the warm history → the exact finite product-weighted sum for fixed permutations, and a finite probability-weighted average over warm permutations with mean Kendall count at most K; reason: conditioning leaves exactly the independent sampling law; averaging it over the warm-order law gives the unconditional inequality in (27), with its mean inversion premise supplied by Lemma 6.1
--   - generalization: the correction decomposition on legal sampled comparison records in the standing admissible domain → the algebraic decomposition for every transcript and all natural dimensions, with absent-answer indicators defined as zero; reason: the score identity is algebraic for arbitrary observed indicators and every permutation pair; legal source records are included unchanged
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §6.2, equations (26)–(27), p. 29, PDF p. 30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Correction

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Equations (26)–(27), p. 29 / PDF 30: the conditional identity and moment,
and the unconditional bound for any warm-order law with mean inversion count at most K. -/
theorem equations_26_27 (n : ℕ) (r π : Rank n) (p : ℝ) (hp : 0 < p ∧ p ≤ 1) :
    (∀ (mask : Pair n → Bool) (T : Transcript n) (i : Fin n),
      correctedScore π T p mask i - rankVector r i =
        samplingNoise r π p mask i + erroneousFlow r π T p mask i) ∧
    (∑ mask : Pair n → Bool,
      (∏ e, if mask e then p else 1 - p) * euclideanNorm (samplingNoise r π p mask) ^ 2) =
      2 * (1 / p - 1) * kendallCount r (rankVector π) ∧
    (∀ (μ : Rank n → ℝ) (K : ℝ),
      (∀ σ, 0 ≤ μ σ) → (∑ σ, μ σ) = 1 →
      (∑ σ, μ σ * (kendallCount r (rankVector σ) : ℝ)) ≤ K →
      (∑ σ, μ σ * (∑ mask : Pair n → Bool,
        (∏ e, if mask e then p else 1 - p) *
          euclideanNorm (samplingNoise r σ p mask) ^ 2)) ≤ 2 * K / p) := by sorry

end RankingQueryCost.Joint
