-- Prove2me | Theorems.Thm_ReplicableOL_lemma_A_8
-- name    : ReplicableOL.lemma_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:49:21.657875+00:00
-- url     : https://prove2.me/theorems/0da3aded-8c2c-46bf-9f2e-cf958a7380fe
-- title:
--   Lemma A.8 — score identity
-- statement:
--   Let $v(\mu)=\frac14-\mu^2$, let $Z=|S|-L(\frac12+\mu)$ and let $q_f(\mu)=\mathbb E[f(S)\mid\mu]$ for $S\sim\mathrm{Bern}(\frac12+\mu)^{\otimes L}$. For every $f:\{0,1\}^L\to[0,1]$, every $c\in\mathbb R$ and every $\mu\in[-\frac14,\frac14]$,
--   $$
--   q_f'(\mu)=\frac{\mathbb E[(f(S)-c)Z\mid\mu]}{v(\mu)},\qquad |q_f'(\mu)|\le\frac{\sqrt L}{2\sqrt{v(\mu)}}\le\beta_L,\quad \beta_L=\frac{2}{\sqrt3}\sqrt L.
--   $$
--   Hence $|q_f(\mu)-q_f(\mu')|\le\beta_L|\mu-\mu'|$ on $[-\Delta,\Delta]$ for $\Delta\le\frac14$.
--
--   The Lipschitz bound is what makes the ambiguity interval of Lemma A.10 long.
--
--   Differences from the source:
--   - encoding: $\mathbb E[(f(S)-c)Z\mid\mu]$ → the finite sum $\sum_sb_s(\mu)(f(s)-c)(|s|-L(1/2+\mu))$; reason: the definition of the conditional expectation given $\mu$
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma A.8, p.29

import Mathlib
import Definitions.Def_ReplicableOL_Block
import Definitions.Def_ReplicableOL_blockWeight
import Definitions.Def_NoSignalPA_ones
import Definitions.Def_ReplicableOL_qf
import Definitions.Def_ReplicableOL_betaL
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma A.8.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma A.8, p.29. `v(μ) = 1/4 − μ²`, `Z = |S| − L(1/2 + μ)`, and `E[(f(S) − c)Z | μ]` is the finite sum over blocks.

**Formalization Note.** The derivative is stated with `HasDerivAt` at each `μ ∈ [−1/4, 1/4]`, for every `c`; `q_f` is a polynomial, defined on all of `ℝ`. `|s|` is the published `NoSignalPA.ones`, the number of ones of a bit string. -/
theorem lemma_A_8 {L : ℕ} (f : Block L → ℝ) (hf : ∀ s, f s ∈ Set.Icc (0 : ℝ) 1) :
    (∀ c μ : ℝ, μ ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4) →
      HasDerivAt (qf f)
        ((∑ s : Block L, blockWeight μ s * (f s - c) * ((NoSignalPA.ones s : ℝ) - (L : ℝ) * (1 / 2 + μ))) / (1 / 4 - μ ^ 2)) μ ∧
      |(∑ s : Block L, blockWeight μ s * (f s - c) * ((NoSignalPA.ones s : ℝ) - (L : ℝ) * (1 / 2 + μ))) / (1 / 4 - μ ^ 2)| ≤
        √(L : ℝ) / (2 * √(1 / 4 - μ ^ 2)) ∧
      √(L : ℝ) / (2 * √(1 / 4 - μ ^ 2)) ≤ betaL L) ∧
    (∀ Δ : ℝ, Δ ≤ 1 / 4 → ∀ μ ∈ Set.Icc (-Δ) Δ, ∀ μ' ∈ Set.Icc (-Δ) Δ,
      |qf f μ - qf f μ'| ≤ betaL L * |μ - μ'|) := by sorry

end ReplicableOL
