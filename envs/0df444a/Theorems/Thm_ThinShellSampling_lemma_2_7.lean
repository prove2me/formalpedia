-- Prove2me | Theorems.Thm_ThinShellSampling_lemma_2_7
-- name    : ThinShellSampling.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:13.206916+00:00
-- url     : https://prove2.me/theorems/712cb766-44a0-4cb3-a7d4-081f7096351d
-- title:
--   Lemma 2.7 — bias from conditioning on success (general form)
-- statement:
--   Let $(\Omega,\mathbb P)$ be a probability space, $X$ a random variable, $S$ an event with $\mathbb P(S)\ge1-\eta$ for some $\eta<1$, and $\pi^X$ a probability measure. Let $\pi^X_N=\operatorname{law}(X)$ and $\hat\pi^X_N=\operatorname{law}(X\mid S)$. Then
--
--   $$
--   \frac{d\hat\pi^X_N}{d\pi^X_N}\le\frac{1}{1-\eta},\qquad \mathsf R_\infty(\hat\pi^X_N\,\|\,\pi^X_N)\le\log\frac{1}{1-\eta},
--   $$
--
--   and for every $q>1$,
--
--   $$
--   \mathsf R_q(\hat\pi^X_N\,\|\,\pi^X)\le\mathsf R_q(\pi^X_N\,\|\,\pi^X)+\frac{q}{q-1}\log\frac{1}{1-\eta}.
--   $$
--
--   In the paper $X$ is the output of the uncapped sampler after $N$ iterations and $S$ is the event that no rejection loop exceeds its cap; on $S$ the capped and uncapped runs agree, so the output of a successful capped run has law $\hat\pi^X_N$. The lemma bounds the bias that conditioning on success introduces.
--
--   **Formalization Note** $d\hat\pi/d\pi\le c$ is the measure inequality $\hat\pi\le c\,\pi$.
--
--   Differences from the source:
--
--   - generalization: X_N the output of PS_unif and S the event that no failure is declared → an arbitrary measurable random variable X and measurable event S with P(S) ≥ 1 − η; reason: the proof uses only the density-ratio bound; PS_unif is the special case, and the proof of Theorem 1.7 applies the same bound to the lifted sampler
--   - encoding: η unrestricted → η < 1; reason: log 1/(1 − η) is undefined otherwise; the paper uses η ∈ (0, 1/2)
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Lemma 2.7, p.18 (PDF p.20); applied in the proof of Theorem 1.7, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Lemma 2.7 (Bias from success), general form.**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Lemma 2.7, p.18 (PDF p.20): "Let `S` be the event that the failure is not declared over the
required `N` iterations, and suppose `P(S) ≥ 1 − η`. Let `π^X_N` be the law of the uncapped `PS_unif`
output after `N` iterations, and `π̂^X_N` be the law of `PS_unif` conditioned on `S` (i.e.,
`π̂^X_N := law(X_N | S)`). Then, `dπ̂^X_N/dπ^X_N ≤ 1/(1 − η)` so `R_∞(π̂^X_N ‖ π^X_N) ≤ log 1/(1 − η)`,
`R_q(π̂^X_N ‖ π^X) ≤ R_q(π^X_N ‖ π^X) + q/(q − 1) log 1/(1 − η)` for `q > 1`."

**Formalization Note.** Stated for an arbitrary random variable `X` on a probability space and an
arbitrary event `S` with `P(S) ≥ 1 − η`, `η < 1` (the density-ratio argument the proof uses, and the
form applied in the proof of Theorem 1.7, p.41); `PS_unif` is the special case. On the event `S` the
capped and uncapped runs coincide, so `law(X | S)` is the conditional law of the uncapped output.
`dπ̂/dπ ≤ c` is the measure inequality `π̂ ≤ c • π`. -/
theorem lemma_2_7 {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → β) (hX : Measurable X) (S : Set Ω) (hS : MeasurableSet S)
    (η : ℝ) (hη : η < 1) (hPS : ENNReal.ofReal (1 - η) ≤ P S) (πX : Measure β)
    [IsProbabilityMeasure πX] :
    (ProbabilityTheory.cond P S).map X ≤ ENNReal.ofReal (1 / (1 - η)) • P.map X ∧
    renyiInf ((ProbabilityTheory.cond P S).map X) (P.map X) ≤
      ENNReal.ofReal (Real.log (1 / (1 - η))) ∧
    ∀ q : ℝ, 1 < q →
      renyi q ((ProbabilityTheory.cond P S).map X) πX ≤
        renyi q (P.map X) πX + ENNReal.ofReal (q / (q - 1) * Real.log (1 / (1 - η))) := by sorry

end ThinShellSampling
