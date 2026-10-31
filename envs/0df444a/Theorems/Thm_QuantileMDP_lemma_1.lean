-- Prove2me | Theorems.Thm_QuantileMDP_lemma_1
-- name    : QuantileMDP.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:01.693319+00:00
-- url     : https://prove2.me/theorems/9ea7c683-99dd-42fa-a6bc-421a829a0d40
-- title:
--   Lemma 1 — the quantile is non-decreasing and left continuous in $\tau$, and $P(X\le Q_\tau(X))\ge\tau$
-- statement:
--   Let $\mu$ be a probability law on $\mathbb R$, the distribution of a random variable $X$, and let $Q_\tau=Q_\tau(\mu)$ be its $\tau$-quantile (Definition 1, footnote 1), with values in $[-\infty,+\infty]$. Then
--
--   1. $\tau\mapsto Q_\tau$ is non-decreasing on $[0,1]$;
--   2. $\tau\mapsto Q_\tau$ is left continuous at every $\tau\in(0,1]$ (as a function on $[0,1]$);
--   3. for every $\tau\in[0,1]$,
--   $$
--   P\bigl(X\le Q_\tau(X)\bigr)\ \ge\ \tau .
--   $$
--
--   These are the basic properties of the quantile used throughout the dynamic programming of the paper; in particular the third one says that the $\tau$-quantile is attained.
--
--   **Formalization Note** No boundedness or finiteness hypothesis is placed on $X$; the quantile is extended-real valued.
--
--   Differences from the source:
--   - encoding: a random variable $X$ → its law $\mu$, an arbitrary probability measure on $\mathbb R$; reason: the quantile and $P(X\le c)$ depend on $X$ only through its law.
--   - encoding: $Q_0=\inf\{X\}$, $Q_1=\sup\{X\}$ → the essential infimum and supremum of footnote 1, valued in the extended reals; reason: footnote 1 gives the precise form, and $\pm\infty$ occur for unbounded $X$.
--   - encoding: "left continuous … function of $\tau$" → continuity within $[0,\tau]$ at each $\tau\in(0,1]$; reason: $[0,1]$ is the domain on which Definition 1 defines $Q_\tau$, and left continuity at $0$ is vacuous.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.1, Lemma 1, p.9

import Mathlib
import Definitions.Def_QuantileMDP_quantile

open MeasureTheory

namespace QuantileMDP

/-- Lemma 1: for a random variable `X` with law `μ`, `τ ↦ Q_τ(X)` is non-decreasing and left
continuous on `[0,1]`, and `P(X ≤ Q_τ(X)) ≥ τ`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §3.1, Lemma 1, p.9.

**Formalization Note** Stated for every probability measure `μ` on `ℝ` (the law of `X`), with the
`EReal`-valued quantile of Definition 1 and footnote 1. Left continuity is continuity within
`[0, τ]` at every `τ ∈ (0, 1]`; the event `{X ≤ Q_τ(X)}` is `{x | (x : EReal) ≤ Q_τ}`. -/
theorem lemma_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MonotoneOn (quantile μ) (Set.Icc 0 1) ∧
      (∀ τ ∈ Set.Ioc (0 : ℝ) 1, ContinuousWithinAt (quantile μ) (Set.Icc 0 τ) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ENNReal.ofReal τ ≤ μ {x : ℝ | (x : EReal) ≤ quantile μ τ}) := by sorry

end QuantileMDP
