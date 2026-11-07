-- Prove2me | Theorems.Thm_RankingCertGap_lemma_5
-- name    : RankingCertGap.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:54:06.452+00:00
-- url     : https://prove2.me/theorems/16a4cf46-52d2-4984-8bc3-354317cccb8f
-- title:
--   Lemma 5, p.19 — score of the power-filter gadget, over $\mathcal A$
-- statement:
--   For all integers $p,q\ge0$, every $f\in\mathcal A$, and every interleaving of the filters of $G_{p,q}$ before $j^\star$,
--
--   $$
--   \Phi_{G_{p,q}}(i^\star,j^\star;f)=\Psi_{p,q}(f)=\frac{p+q+1}{(p+1)(q+1)}+\int_0^1\Bigl(1-y^p-y^q+\frac{y^{p+q+1}}{p+1}\Bigr)f(y)\,dy.
--   $$
--
--   The ordered pair $(p,q)$ is not symmetric: $p$ belongs to the distinguished endpoint $i^\star$ and $q$ to the other root. This is the exact score of the family of instances that realizes the degree-two constraints.
--
--   Differences from the source:
--   - generalization: Lemma 5 prints $f\in\mathcal F$ → $f\in\mathcal A$; reason: the source claims this extension on p.20 and p.86, since its proof uses only measurability, $0\le f\le1$ and $f(1)=1$; $\mathcal F\subseteq\mathcal A$, so the printed lemma is a special case
--   - encoding: "the two filter sequences may be interleaved arbitrarily" → every arrival order of the filters that keeps $j^\star$ last; reason: an order within one filter sequence is a relabelling of its filters; $\sigma=1$ is the reference order
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
--   - encoding: $f:[0,1]\to[0,1]$ → $f:\mathbb R\to\mathbb R$ with values in $[0,1]$ everywhere; reason: a printed $f$ extends (for instance by $0$), and scores read $f$ only on $[0,1]$ almost surely; same suprema and scores
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Lemma 5, p.19; Remarks, p.20; App. E.1.4; App. M, p.86

import Mathlib
import Definitions.Def_RankingCertGap_CertifyingCapacity
import Definitions.Def_RankingCertGap_PowerFilter

namespace RankingCertGap

/-- **Lemma 5 (Score of the power-filter gadget), over `𝒜`.** Xu, arXiv:2610.17545 (held file sha256
75896dd9…), Lemma 5, p.19 with the extension of p.20 and p.86: for every `p, q ∈ ℤ_{≥0}` and `f ∈ 𝒜`,
`Φ_{G_{p,q}}(i★, j★; f) = Ψ_{p,q}(f)` (eq. (41)).

**Formalization Note.** The numbered lemma prints `f ∈ ℱ`. The remarks on p.20 and p.86 state that it
remains valid for `f ∈ 𝒜`, and the goal needs that version. The page allows the two filter sequences
to be interleaved arbitrarily, so the statement quantifies over every order `σ` that keeps `j★` last;
`σ = 1` is `powerFilter p q`. -/
theorem lemma_5 (p q : ℕ) (f : ℝ → ℝ) (hf : f ∈ classA) (σ : Equiv.Perm (Fin (p + q + 1)))
    (hσ : σ (powerFilter.jStar p q) = powerFilter.jStar p q) :
    (powerFilter.reorder p q σ).Phi (powerFilter.iStar p q) (powerFilter.jStar p q) f =
      Psi p q f := by sorry

end RankingCertGap
