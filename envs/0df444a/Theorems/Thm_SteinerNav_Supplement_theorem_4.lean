-- Prove2me | Theorems.Thm_SteinerNav_Supplement_theorem_4
-- name    : SteinerNav.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:14:00.206802+00:00
-- url     : https://prove2.me/theorems/6c238707-cd54-48cc-8b42-ff313dd26255
-- title:
--   Theorem 4 — general lower bound $n^2\gamma/(4096\ln(2/\gamma))$ edges on the two-shell instance, with probability $\ge1-1/n$
-- statement:
--   Let $c_0=128$, let $n\ge4$ be even, $m=n/2$, let $1<\alpha\le2$ and $\gamma=\alpha-1$, and suppose
--   $$(d-1)\gamma\ge c_0\ln n .$$
--   Let $P=S\cup T$ be the two-shell instance in $\mathbb R^d$: $T$ consists of $m$ independent uniformly random unit vectors and $S$ of $m$ independent uniformly random vectors of norm $\gamma/2$, all $n$ vectors independent. Then with probability at least $1-1/n$, every $\alpha$-navigable graph with Steiner points on $P$ (any finite set $R$ of Steiner points and any edge set $E$ satisfying Definition 1) has at least
--   $$\frac{n^2\gamma}{4096\,\ln(2/\gamma)}$$
--   edges.
--
--   This general lower bound grows with $\gamma$, from $\Omega(n^2\log n/(d\log d))$ edges at $\gamma\approx\log n/d$ to $\Omega(n^2)$ for constant $\gamma$, and it is the engine of the main lower bound (Theorem 2).
--
--   **Formalization Note** The probability space is the product of $2m$ copies of the uniform law on the unit sphere (`twoShellLaw`). Because the event quantifies over all graphs, the statement asserts a measurable set $G$ of probability at least $1-1/n$ on every outcome of which the edge bound holds for every $R$ and $E$.
--
--   Differences from the source:
--   - encoding: "with probability at least 1 − 1/n, every graph … has at least … edges" → there is a measurable set of outcomes of probability at least 1 − 1/n on which the bound holds for every graph; reason: the event quantifies over uncountably many graphs and need not be measurable a priori; a measurable subset of the stated probability is the source's claim whenever the event is measurable, and is never weaker.
--   - encoding: the instance P as a set of n points → the finite set of the 2m sampled points; reason: samples coincide only on a null set, which is excluded by the probability bound.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee62135a42ef49d815773f6af7f50ba344b9460d6007d849529b707b183), Theorem 4, p.13 (PDF p.13); instance §5.1, p.10; proof pp.14–15

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_Supplement_twoShell

namespace SteinerNav.Supplement

open MeasureTheory

/-- Theorem 4 (general lower bound): let `c₀ = 128`, let `n ≥ 4` be even, `m = n/2`, `1 < α ≤ 2` and
`γ = α − 1`, and suppose `(d − 1)γ ≥ c₀ ln n`. With probability at least `1 − 1/n` over the two-shell
instance `P` (`m` independent uniform unit vectors as targets, `m` independent uniform vectors of norm
`γ/2` as sources), every `α`-navigable graph with Steiner points on `P` has at least
`n²γ/(4096 ln(2/γ))` edges (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 4, p.13; instance §5.1, p.10).

**Formalization Note** The event quantifies over all finite `R` and all `E`, so it is stated through
a measurable set `G` of probability at least `1 − 1/n` on every point of which the bound holds (so the
event contains a measurable set of that probability). Logarithms are natural. -/
theorem theorem_4 (d n : ℕ) (hn : 4 ≤ n) (hev : Even n) (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (hd : 128 * Real.log n ≤ ((d : ℝ) - 1) * (α - 1)) :
    ∃ G : Set (TwoShellSpace (n / 2) d), MeasurableSet G ∧
      ENNReal.ofReal (1 - 1 / (n : ℝ)) ≤ twoShellLaw (n / 2) d G ∧
      ∀ ω ∈ G, ∀ (R : Finset (Pt d)) (E : Finset (Pt d × Pt d)),
        IsSteinerNavigable α (twoShell (α - 1) ω) R E →
          (n : ℝ) ^ 2 * (α - 1) / (4096 * Real.log (2 / (α - 1))) ≤ (E.card : ℝ) := by sorry

end SteinerNav.Supplement
