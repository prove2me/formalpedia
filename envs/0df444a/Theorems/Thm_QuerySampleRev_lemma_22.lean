-- Prove2me | Theorems.Thm_QuerySampleRev_lemma_22
-- name    : QuerySampleRev.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:29.359555+00:00
-- url     : https://prove2.me/theorems/bfa8ee2a-e6fe-4fa6-bf48-2fd0770a8b9e
-- title:
--   Lemma 22 — the base and hard distributions are quasi-MHR
-- statement:
--   Let $c\in[0,1]$ and $0<\varepsilon\le1/128$. The base distribution $F^{(0)}$ and the hard distributions $F^{(i)}$, $i\in[K]$, are quasi-MHR distributions: each is a probability distribution on $[0,\infty)$ with finite optimal revenue, and its ratio $-\log Q(p)/p$ (with value $+\infty$ where $Q(p)=0$) is nondecreasing for $p>0$.
--
--   Together with the good-price separation, this shows that a PAC learner for the quasi-MHR family must succeed on each of the $K+1$ instances of the construction.
--
--   Differences from the source:
--   - encoding: quasi-MHR distribution → membership in the family: probability measure on $[0,\infty)$, quasi-MHR, finite $r^*$; reason: the standing assumptions of §2.1–2.2 on value distributions
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Lemma 22, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_QuerySampleRev_InFamily
import Definitions.Def_QuerySampleRev_hardDist

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **Lemma 22 (Quasi-MHR).** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization*
(manuscript, sha256 c31ea3d3…), Lemma 22, p.36 (PDF 38): "The base distribution `F⁽⁰⁾` and the hard
distributions `{F⁽ⁱ⁾}_{i∈[K]}` are quasi-MHR distributions."

For `c ∈ [0, 1]` and `0 < ε ≤ 1/128` (the parameter range of Theorem 21, under which the construction is
made), `baseDist` and every `hardDist ε c i` with `i ∈ [K]` belong to the quasi-MHR family: probability
measures on `[0, ∞)`, quasi-MHR, with finite optimal revenue. -/
theorem lemma_22 {c ε : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hε0 : 0 < ε) (hε : ε ≤ 1 / 128) :
    InFamily baseDist ∧ ∀ i ∈ Finset.Icc 1 (numHard ε c), InFamily (hardDist ε c i) := by sorry

end QuerySampleRev
