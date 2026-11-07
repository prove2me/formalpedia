-- Prove2me | Theorems.Thm_RankingCertGap_lemma_22
-- name    : RankingCertGap.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:54:52.204914+00:00
-- url     : https://prove2.me/theorems/863a22dd-8a50-4004-a978-dcea512641d4
-- title:
--   Lemma 22, p.34 — constant gain-sharing certificate
-- statement:
--   The profile $\tilde f^\star_2$, equal to $3/4$ on $[0,1)$ and to $1$ at $1$, belongs to $\mathcal F$, and
--
--   $$
--   \tilde\chi(\tilde f^\star_2;2)=\frac34.
--   $$
--
--   So the supremum defining $\tilde\Gamma_{\mathcal A}(2)$ is at least $3/4$.
--
--   Differences from the source:
--   - encoding: $\tilde f^\star_2$ on $[0,1]$ → $\tilde f^\star_2(y)=1$ also for $y>1$; reason: values off $[0,1]$ are never read by a score, and this keeps the extension $[0,1]$-valued
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Lemma 22, eq. (107), p.34; eq. (27), p.10

import Mathlib
import Definitions.Def_RankingCertGap_CertifyingCapacity

namespace RankingCertGap

/-- **Lemma 22 (Constant gain-sharing certificate).** Xu, arXiv:2610.17545 (held file sha256 75896dd9…),
Lemma 22, p.34: "For the admissible profile `f̃★₂ ∈ ℱ`, `χ̃(f̃★₂; 2) = 3/4`" (eq. (107)). The profile is
eq. (27), p.10. -/
theorem lemma_22 : fTilde ∈ classF ∧ chiC fTilde (regular 2) = 3 / 4 := by sorry

end RankingCertGap
