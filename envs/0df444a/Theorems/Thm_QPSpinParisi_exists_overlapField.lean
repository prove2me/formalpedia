-- Prove2me | Theorems.Thm_QPSpinParisi_exists_overlapField
-- name    : QPSpinParisi.exists_overlapField
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:05:57.868044+00:00
-- url     : https://prove2.me/theorems/9dda63b3-5578-4bcc-8404-d7d5e6b15057
-- title:
--   p.11 — the Gaussian field $Y_n$ with covariance $n\xi(q(s,t))$ exists
-- statement:
--   For every $n$ there is a centered Gaussian process $(Y_n(s))_{s\in(S^2)^n}$ with
--   $$\mathbb E\,Y_n(s)Y_n(t)=n\,\xi(q(s,t))$$
--   and almost surely continuous paths. For infinite mixtures the series over $p$ has to be controlled uniformly. This is the comparison process of Lemma 3.2, and it shows that the statements quantifying over all realizations of $Y_n$ are not vacuous.
--
--   Differences from the source:
--   - reading: $Y_n=\sum_pc_pY_{n,p}$ "has covariance $n\xi(q(s,t))$" → a realization with this covariance exists, with almost surely continuous paths; reason: the source maximizes $Y_n$ and integrates it over $(S^2)^n$, which needs continuous paths
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.11 (PDF p.11)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_OverlapField

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.11, PDF p.11 (the construction before Lemma 3.2): a centered Gaussian process `Y_n` on `(S²)ⁿ` with covariance
`E Y_n(s) Y_n(t) = n ξ(q(s,t))` and almost surely continuous paths exists. Every statement quantifying over the field is non-vacuous by
this item. -/
theorem exists_overlapField (c : ℕ → ℝ) (hc : MixHyp c) (n : ℕ) : Nonempty (OverlapField c n) := by sorry

end QPSpinParisi
