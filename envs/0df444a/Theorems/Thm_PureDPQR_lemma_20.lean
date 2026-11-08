-- Prove2me | Theorems.Thm_PureDPQR_lemma_20
-- name    : PureDPQR.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:57.84707+00:00
-- url     : https://prove2.me/theorems/3df0da53-d78e-46f1-8e40-ae4d609d9ba5
-- title:
--   Lemma 20, p.22 — bounded martingale estimate $\sum_{t=1}^TM_t\le b\sqrt{2T\log(1/\theta)}$ w.p. $\ge1-\theta$
-- statement:
--   **Lemma 20** (A bounded martingale estimate). Let $(\mathcal F_t)_{t=0}^T$ be a filtration on a probability space, and let $M_t$ ($t=1,\dots,T$) be $\mathcal F_t$-measurable with $\mathbb E[M_t\mid\mathcal F_{t-1}]=0$ and $|M_t|\le b$ almost surely, where $b>0$. For $0<\theta<1$, with probability at least $1-\theta$,
--
--   $$\sum_{t=1}^TM_t\le b\sqrt{2T\log(1/\theta)} .$$
--
--   It supplies the concentration step of Proposition 21.
--
--   **Formalization Note** The filtration is indexed by $\mathbb N$ and only $\mathcal F_0,\dots,\mathcal F_T$ are used. The conditional expectation is Mathlib's; the increments are bounded and measurable, hence integrable.
--
--   Differences from the source:
--   - encoding: a filtration (F_t)_{t=0}^T → a filtration indexed by ℕ, hypotheses imposed for t ∈ {1, …, T}; reason: a finite filtration extends by F_t = F_T for t > T; same statement
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Lemma 20, p.22 (PDF p.23)

import Mathlib

open MeasureTheory

namespace PureDPQR

/-- **Lemma 20** (A bounded martingale estimate), p.22 (PDF p.23).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"Let (F_t)_{t=0}^T be a filtration, and let M_t be F_t-measurable with E[M_t | F_{t−1}] = 0 and
|M_t| ≤ b almost surely, where b > 0. For 0 < θ < 1, with probability at least 1 − θ,
∑_{t=1}^T M_t ≤ b √(2T log(1/θ))."

**Formalization Note.** The filtration is indexed by `ℕ`; only `ℱ 0, …, ℱ T` are used (a finite
filtration extends by `ℱ t = ℱ T` for `t > T`). The hypotheses are imposed for
`t ∈ {1, …, T}`. `E[M_t | F_{t−1}]` is Mathlib's conditional expectation `μ[M t | ℱ (t − 1)]`; the
increments are bounded and measurable, hence integrable, so it is the genuine conditional
expectation. Probabilities are `ℝ≥0∞`-valued. -/
theorem lemma_20 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (T : ℕ) (M : ℕ → Ω → ℝ) (b : ℝ) (hb : 0 < b)
    (hmeas : ∀ t ∈ Finset.Icc 1 T, StronglyMeasurable[ℱ t] (M t))
    (hmart : ∀ t ∈ Finset.Icc 1 T, μ[M t | ℱ (t - 1)] =ᵐ[μ] 0)
    (hbdd : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂μ, |M t ω| ≤ b)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ENNReal.ofReal (1 - θ) ≤
      μ {ω | ∑ t ∈ Finset.Icc 1 T, M t ω ≤ b * Real.sqrt (2 * (T : ℝ) * Real.log (1 / θ))} := by sorry

end PureDPQR
