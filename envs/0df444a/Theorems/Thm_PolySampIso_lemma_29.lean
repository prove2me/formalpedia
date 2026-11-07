-- Prove2me | Theorems.Thm_PolySampIso_lemma_29
-- name    : PolySampIso.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:13.432896+00:00
-- url     : https://prove2.me/theorems/137f1432-32b1-45b5-b4be-034e3fca2387
-- title:
--   Lemma 29, p.39 — correctness of Algorithm 5 (FunctionalCooling)
-- statement:
--   There is a constant $C'>0$ (the constant of Corollary 3) such that the following holds. Let $X$ be a nonempty bounded polytope with $m$ constraints in $\mathbb R^n$, $\delta\in(0,\tfrac12)$ and $T=C'(m+\sqrt n\log(m/\delta))$. Let $\hat x\in X$ satisfy $\|\nabla\psi(\hat x)\|_{\hat x,*}\le1/(100\sqrt{t_1D})$, and let $\{O_t\}_{t\ge0}$ be any family with each $O_t$ a $(3,\delta/(2T))$-$\chi^2$-to-TV oracle for $\pi_t$. Then the output $x$ of Algorithm 5 run with these oracles satisfies
--
--   $$\mathrm{TV}(\mathrm{Law}(x),\pi)\le\delta.$$
--
--   The cooling framework reduces sampling $\pi$ from a cold start to at most $T$ warm-start sampling problems, at no loss beyond the accumulated oracle errors; Theorem 2 follows by plugging in Algorithm 7 (Proposition 8).
--
--   Differences from the source:
--   - generalization: x̂ ← AnalyticCenter(X, 1/(100√(tD))) (Algorithm 5, line 3) → any x̂ ∈ X with ‖∇ψ(x̂)‖_{x̂,∗} ≤ 1/(100√(t₁D)); reason: the proof uses only this guarantee (via Lemma 24); AnalyticCenter's output is such a point
--   - encoding: T := C′(m + √n log(m/δ)) for the constant C′ in Corollary 3 → ∃ C′ > 0 chosen before all instance data, T = C′(m + √n log(m/δ)) independent of the oracles; reason: Corollary 3's constant is universal
--   - encoding: oracles {Ot}t≥0, Ot a (3, δ/(2T))-χ²-to-TV oracle for πt → a family of kernels O t with IsChiSqToTVOracle X (O t) π_t 3 (δ/(2T)) for every t ≥ 0; reason: kernel form of Definition 8 (Pₜ(x, ·) := Law(Oₜ(x)), p.39)
--   - encoding: the run of Algorithm 5 → coolingLaw: phase1Law composed with the oracle kernels at the explicit temperature list of Phases 2–4; reason: both while loops terminate (p.35–36); the list is their trace
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 29, p.39 (PDF p.41); Algorithm 5's input line, p.33; Corollary 3, p.36

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_ChiSqToTVOracle
import Definitions.Def_PolySampIso_FunctionalCooling

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Lemma 29** (correctness of Algorithm 5).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 29, p.39 (PDF p.41), with the input line of
Algorithm 5, p.33 (PDF p.35):

"Lemma 29. The output x of Algorithm 5 satisfies TV(Law(x), π) ≤ δ."
"Input: target error δ ∈ (0, 1/2), oracles {Ot}t≥0 where Ot is a (3, δ/(2T))-χ2-to-TV oracle for πt,
T := C′(m + √n log(m/δ)) for the constant C′ in Corollary 3"

**Formalization Note.** `C′` (Corollary 3's constant) is chosen before all instance data, and `T`
depends only on `m, n, δ`, not on the oracles. The oracles are any family of kernels `O t`
(`t ≥ 0`) each a `(3, δ/(2T))`-χ²-to-TV oracle for `π_t` (Definition 8, which includes that `O t`
is a Markov kernel from `X` to `X`). `x̂` (line 3) is any point of `X` with the guarantee of
Proposition 5, `‖∇ψ(x̂)‖_{x̂,∗} ≤ 1/(100√(t₁D))`. `coolingLaw` is the law of the output of
Algorithm 5 (Phase 1, then the oracle calls of Phases 2–4 in order, with fresh randomness). The
standing assumption of §2.3 is kept. -/
theorem lemma_29 :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), StandingAssumption A b →
        0 < n → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∀ xhat ∈ polytope A b,
          dualLocalNorm A b xhat (gradLogBarrier A b xhat) ≤
            1 / (100 * Real.sqrt (coolT1 n δ * coolD n δ)) →
        ∀ O : ℝ → Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
          (∀ t : ℝ, 0 ≤ t → IsChiSqToTVOracle (polytope A b) (O t) (cooled A b t) 3
            (δ / (2 * (C' * (m + Real.sqrt n * Real.log (m / δ)))))) →
          tvDist (coolingLaw A b δ xhat O) (uniform A b) ≤ δ := by sorry

end PolySampIso
