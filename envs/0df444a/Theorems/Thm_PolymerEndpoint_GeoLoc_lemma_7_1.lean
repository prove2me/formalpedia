-- Prove2me | Theorems.Thm_PolymerEndpoint_GeoLoc_lemma_7_1
-- name    : PolymerEndpoint.GeoLoc.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:33:55.976995+00:00
-- url     : https://prove2.me/theorems/a097fbff-8a80-4bc1-a6c3-34fe65818194
-- title:
--   Lemma 7.1, p. 47 — W_δ is upper, m and Q are lower semicontinuous on 𝒮
-- statement:
--   Let $d\ge1$ and let $W_\delta$, $m$ and $Q$ be the functionals of §7.1 on the space $\mathcal S$ of partitioned subprobability measures.
--
--   1. For any $\delta\in(0,1)$, $W_\delta:\mathcal S\to\mathbb N\cup\{0,\infty\}$ is upper semicontinuous and thus measurable.
--   2. $m:\mathcal S\to[0,1]$ is lower semicontinuous and thus measurable.
--   3. $Q:\mathcal S\to[0,\infty]$ is lower semicontinuous and thus measurable.
--
--   Part 1 makes $\mathcal V_{\delta,K}=\{W_\delta\le K\}$ open and part 2 makes $\{m>1-\delta\}$ open; both are used, through the portmanteau theorem, to pass from the limit set $\mathcal M$ to the Cesàro densities in Theorem 7.3.
--
--   **Formalization Note.** $W_\delta$ takes values in $\mathbb N\cup\{\infty\}$ and $Q$ in $[0,\infty]$, with their order topologies.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 47, Lemma 7.1

import Mathlib
import Definitions.Def_PolymerEndpoint_GeoLoc_Functionals
open MeasureTheory

namespace PolymerEndpoint.GeoLoc

/-- Lemma 7.1: (a) `W_δ` is upper semicontinuous for `δ ∈ (0, 1)`; (b) `m` and (c) `Q` are lower
semicontinuous; all three are therefore measurable. -/
theorem lemma_7_1 (d : ℕ) (hd : 1 ≤ d) :
    (∀ δ ∈ Set.Ioo (0 : ℝ) 1, UpperSemicontinuous (Wdelta δ : PolymerEndpoint.Atomic.PSM d → ℕ∞) ∧
        Measurable (Wdelta δ : PolymerEndpoint.Atomic.PSM d → ℕ∞)) ∧
    (LowerSemicontinuous (mfun : PolymerEndpoint.Atomic.PSM d → ℝ) ∧ Measurable (mfun : PolymerEndpoint.Atomic.PSM d → ℝ)) ∧
    (LowerSemicontinuous (Qfun : PolymerEndpoint.Atomic.PSM d → ENNReal) ∧ Measurable (Qfun : PolymerEndpoint.Atomic.PSM d → ENNReal)) := by sorry

end PolymerEndpoint.GeoLoc
