-- Prove2me | Theorems.Thm_SensitivityCampaign_reach_doubled_paley_12047_exact
-- name    : SensitivityCampaign.reach_doubled_paley_12047_exact
-- status  : Open
-- author  : @yousofy
-- created : 2026-10-21T16:55:26.171157+00:00
-- url     : https://prove2.me/theorems/e4ba0749-3735-4f3b-a06c-3c3ed5715a4a
-- title:
--   Sensitivity separation at $8\log(12047)/\log(2084175267334724)$
-- statement:
--   For every real $\varepsilon>0$ and every natural $S\ge2$, there exist a natural number $n$ and a total Boolean function $f:\{0,1\}^n\to\{0,1\}$ such that $s(f)\ge S$ and $bs(f)\ge s(f)^{8\log(12047)/\log(2084175267334724)-\varepsilon}$. The exact endpoint is approximately $2.1311555213827738068\ldots$. This is an open formalization target: the supplied integer certificate and supporting lemmas do not yet constitute a complete Lean proof of this separation.
--
--   ### Independent read-back
--
--   The following was written by an independent Codex auditor given only the Lean code and dependency definitions. It is included here for review in the website editor.
--
--   For every real number $\varepsilon>0$ and every natural number $S\ge 2$, there exist a natural number $n$ and a Boolean function $f:\{0,1\}^{[n]}\to\{0,1\}$, where $[n]=\{0,\ldots,n-1\}$, with the following properties. For an input $x$ and a coordinate subset $B\subseteq[n]$, let $x^B$ be the input obtained by reversing exactly the bits in $B$. Define $s(f)$ to be the maximum, over all inputs $x$, of the number of coordinates $i\in[n]$ such that $f(x^{\{i\}})\ne f(x)$. Define $b(f)$ to be the maximum, over all inputs $x$ and all finite families $\mathcal B$ of distinct, nonempty, pairwise disjoint subsets of $[n]$ satisfying $f(x^B)\ne f(x)$ for every $B\in\mathcal B$, of the number $|\mathcal B|$ of blocks; the empty family is permitted and contributes zero. Then $S\le s(f)$ and $s(f)^{\frac{8\log(12047)}{\log(2084175267334724)}-\varepsilon}\le b(f)$, where both sensitivity values are regarded as real numbers in this inequality, $\log$ denotes the natural logarithm, and the power is a real power. The maxima defining $s(f)$ and $b(f)$ are taken independently and need not occur at the same input. There is no upper bound on $\varepsilon$, so the exponent may be zero or negative; $n$ and $f$ may depend on both $\varepsilon$ and $S$. The quantifier over $n$ includes zero, but when $n=0$ both sensitivity values are zero, so it cannot satisfy $S\le s(f)$ for $S\ge 2$.
-- source:
--   https://github.com/bigospeedrun/site/issues/2

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_finite_certificate
import Theorems.Thm_SensitivityCampaign_finite_certificate_log
open OAI.Paper320

theorem SensitivityCampaign.reach_doubled_paley_12047_exact :
    SensitivityCampaign.AchievesExponent ((8 * Real.log (12047 : ℝ) / Real.log (2084175267334724 : ℝ)) : ℝ) := by sorry
