-- Prove2me | Theorems.Thm_WildeQIT_ZhangAudenaert_maximalCoupling_prob
-- name    : WildeQIT.ZhangAudenaert.maximalCoupling_prob
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:56:39.804734+00:00
-- url     : https://prove2.me/theorems/b5c4f17d-db58-4890-9d2a-c9f73dfa6d05
-- title:
--   Lemma 10.7.2: a maximal coupling has $\Pr\{\hat X=\hat Y\}=\sum_u\min\{p_X(u),p_Y(u)\}$ and $\Pr\{\hat X\ne\hat Y\}=\tfrac12\|p_X-p_Y\|_1$
-- statement:
--   Let $X$ and $Y$ be random variables on a finite alphabet $\mathcal A$ with distributions $p_X$ and $p_Y$. A coupling of $(X,Y)$ is a pair $(\hat X,\hat Y)$ whose marginals are $p_X$ and $p_Y$; it is maximal if $\Pr\{\hat X=\hat Y\}$ is as large as possible among all couplings (Definitions 10.7.2 and 10.7.3). If $(\hat X,\hat Y)$ is a maximal coupling of $X$ and $Y$, then
--
--   $$
--   \Pr\{\hat X=\hat Y\}=\sum_{u\in\mathcal A}\min\{p_X(u),p_Y(u)\},
--   \qquad
--   \Pr\{\hat X\neq\hat Y\}=\tfrac12\|p_X-p_Y\|_1 .
--   $$
--
--   The second identity converts the trace distance into an error probability, which is how Fano's inequality yields the Zhang–Audenaert bound.
--
--   **Formalization Note** A coupling is its joint distribution on $\mathcal A\times\mathcal A$; maximality is the published `FinDist.IsMaximalCoupling`. The lemma is stated for every maximal coupling; their existence is a separate fact established in the book's proof.
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 10.7.2, eqs. (10.103)–(10.104), p. 308

import Mathlib
import Definitions.Def_WildeQIT_coupling
import Definitions.Def_WildeQIT_classicalTraceDist
import Definitions.Def_WildeQIT_ZhangAudenaert_probNe

namespace WildeQIT.ZhangAudenaert

/-- **Lemma 10.7.2.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Lemma 10.7.2,
(10.103)–(10.104), p. 308: "Let `X` and `Y` be discrete random variables taking values in a
finite alphabet `𝒜`. Let `p_X` and `p_Y` denote their distributions, respectively. If `(X̂, Ŷ)` is
a maximal coupling of `X` and `Y`, then the following equalities hold
`Pr{X̂ = Ŷ} = ∑_{u∈𝒜} min{p_X(u), p_Y(u)}`, `Pr{X̂ ≠ Ŷ} = (1/2)‖p_X − p_Y‖₁`."

**Formalization Note.** A coupling `(X̂, Ŷ)` is its joint distribution `c` on `α × α`;
`FinDist.IsMaximalCoupling p q c` (Definitions 10.7.2–10.7.3, published) says that `c` has
marginals `p` and `q` and maximizes `Pr{X̂ = Ŷ} = c.probEq` over all couplings.
`Pr{X̂ ≠ Ŷ} = probNe c`. -/
theorem maximalCoupling_prob {α : Type} [Fintype α] [DecidableEq α] (p q : FinDist α)
    (c : FinDist (α × α)) (hc : FinDist.IsMaximalCoupling p q c) :
    c.probEq = ∑ u, min (p.prob u) (q.prob u) ∧
      probNe c = (1 / 2) * classicalTraceDist p.prob q.prob := by sorry

end WildeQIT.ZhangAudenaert
