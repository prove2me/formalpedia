-- Prove2me | Theorems.Thm_RankingCertGap_lemma_6
-- name    : RankingCertGap.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:54:11.565672+00:00
-- url     : https://prove2.me/theorems/2f6ed2e5-09d7-465b-a76d-4ca77306f933
-- title:
--   Lemma 6, p.19 — exact degree-two edge reduction, over $\mathcal A$
-- statement:
--   For every $f\in\mathcal A$,
--
--   $$
--   \chi(f;2)=\min\Bigl\{H_f(1),\ \inf_{p,q\in\mathbb Z_{\ge0}}\Psi_{p,q}(f)\Bigr\},
--   $$
--
--   where $\chi(f;2)$ is the infimum of $\Phi_G(i,j;f)$ over instances of online degree at most two and their edges, and $H_f(1)=\int_0^1 f(y)\,dy$.
--
--   So the infinite-dimensional adversary reduces to one singleton constraint and a two-parameter family.
--
--   Differences from the source:
--   - generalization: Lemma 6 prints $f\in\mathcal F$ → $f\in\mathcal A$; reason: the source claims this extension on p.20 and p.86; $\mathcal F\subseteq\mathcal A$, so the printed lemma is a special case
--   - encoding: $H_f(1)$ with $H_f(t):=F_f(t)+1-f(t)$ (13) → $H_f(1)=\int_0^1f$; reason: $f(1)=1$; this is (43)
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
--   - encoding: $f:[0,1]\to[0,1]$ → $f:\mathbb R\to\mathbb R$ with values in $[0,1]$ everywhere; reason: a printed $f$ extends (for instance by $0$), and scores read $f$ only on $[0,1]$ almost surely; same suprema and scores
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Lemma 6, p.19; Remarks, p.20; App. M, p.86

import Mathlib
import Definitions.Def_RankingCertGap_CertifyingCapacity
import Definitions.Def_RankingCertGap_PowerFilter

namespace RankingCertGap

/-- **Lemma 6 (Exact degree-two edge reduction), over `𝒜`.** Xu, arXiv:2610.17545 (held file sha256
75896dd9…), Lemma 6, p.19 with the extension of p.20 and p.86: for every `f ∈ 𝒜`,
`χ(f; 2) = min{H_f(1), inf_{p,q ∈ ℤ_{≥0}} Ψ_{p,q}(f)}` (eq. (42)).

**Formalization Note.** The numbered lemma prints `f ∈ ℱ`; see `lemma_5`. `H_f(1) = ∫₀¹ f` by (43).
The infimum is a real `⨅` over `ℕ × ℕ`, a nonempty index set; for `f ∈ 𝒜` the family is bounded below
because each `Ψ_{p,q}(f)` is a score in `[0, 2]` by Lemma 5. -/
theorem lemma_6 (f : ℝ → ℝ) (hf : f ∈ classA) :
    chiC f (onDegLE 2) = min (Hf1 f) (⨅ pq : ℕ × ℕ, Psi pq.1 pq.2 f) := by sorry

end RankingCertGap
