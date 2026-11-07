-- Prove2me | Theorems.Thm_SmoothedMIS_lemma_2_2
-- name    : SmoothedMIS.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:28.056578+00:00
-- url     : https://prove2.me/theorems/dbc352ee-8181-4511-9c0f-7cc789f5ba80
-- title:
--   Lemma 2.2 — diameter of $G(N,q)$ with an explicit failure probability
-- statement:
--   There is an absolute constant $c'\ge1$ with the following property. Let $N\ge1$ be an integer, $0<q\le1/2$, and $\nu=Nq\ge c'(\ln N+1)$. Then $X\sim G(N,q)$ satisfies
--   $$
--   \mathbb P\big[\operatorname{diam}(X)>2r+1\big]\le 3e^{-\nu/c'},\qquad r=\left\lceil\frac{\ln N}{\ln(\nu/8)}\right\rceil+1,
--   $$
--   where $\operatorname{diam}(X)=\infty$ if $X$ is disconnected.
--
--   This is the random-graph input of Lemma 3.1: applied to a quotient graph it shows that large two-hop neighbourhoods have diameter $O(\sqrt{\ln n})$ after smoothing.
--
--   Differences from the source:
--   - reading: r = ⌈ln N/ln(ν/8)⌉ + 1, undefined at ν = 8 (division by ln 1 = 0) → Lean's value r = 1 at ν = 8; reason: the printed formula has no value there; the value ν = 8 is excluded by ν ≥ c'(ln N + 1) for every c' ≥ 8, in particular the paper's c' = 1024
--   - encoding: X ∼ G(N, q) → erGraph ω = fromEdgeSet {e | ω e = true} under independent coins of probability q on Sym2 (Fin N), diagonal pairs ignored; reason: the same random graph
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 2.2, p.10 (PDF p.12); proof App. A, pp.42–44

import Mathlib
import Definitions.Def_SmoothedMIS_ERDiamBound

namespace SmoothedMIS

/-- **Lemma 2.2** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis for Distributed MIS*
(manuscript, sha256 dc2131db…), Lemma 2.2, p.10). There is an absolute constant `c' ≥ 1` such
that for `0 < q ≤ 1/2` and `ν = Nq ≥ c'(ln N + 1)`, `X ∼ G(N, q)` satisfies
`P[diam(X) > 2r + 1] ≤ 3e^{−ν/c'}`, where `r = ⌈ln N/ln(ν/8)⌉ + 1`.

**Formalization Note** The bound for a given `c'` is `ERDiamBound c'`; `diam` is `ediam`
(`∞` when disconnected). App. A proves the lemma with `c' = 1024`. -/
theorem lemma_2_2 : ∃ c' : ℝ, 1 ≤ c' ∧ ERDiamBound c' := by sorry

end SmoothedMIS
