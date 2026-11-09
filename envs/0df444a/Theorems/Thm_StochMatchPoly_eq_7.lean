-- Prove2me | Theorems.Thm_StochMatchPoly_eq_7
-- name    : StochMatchPoly.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:29:42.736531+00:00
-- url     : https://prove2.me/theorems/5eaae189-9a24-4045-8399-a899904b7413
-- title:
--   Eq. (7) — the perturbed optimum has total covariance at most $8\sum_i\mathbb E X^\theta_i$
-- statement:
--   Let $G(\omega)$ be the random subgraph of a finite simple graph $G=(V,E)$ with independent edges of probabilities $q_e\in[0,1]$. Fix $\theta\in\mathbb R^V$, let $\xi_v\sim\mathrm{Unif}[-1,1]$ be independent across vertices and of $\omega$, let $M^\theta$ be the matching of $G(\omega)$ maximizing $\sum_{v\in V(M)}(\theta_v+\xi_v)$, and $X^\theta_v=\mathbf 1\{v\in V(M^\theta)\}$. Then
--
--   $$\sum_{u,v\in V}\bigl|\operatorname{Cov}(X^\theta_u,X^\theta_v)\bigr|\le 8\sum_{i\in V}\mathbb E X^\theta_i ,$$
--
--   the sum over ordered pairs including the diagonal.
--
--   This is the covariance half of Lemma 3.1: maximizing randomly perturbed vertex weights gives a matching whose total pairwise covariance is linear in its expected number of matched vertices.
--
--   Differences from the source:
--   - encoding: X^θ_v = 1{v ∈ V(M^θ)} for the matching M^θ maximizing the covered-vertex weight, unique almost surely → coverIndicator S (θ + ξ) v = 1 iff some matching of S covering v scores strictly more than every matching of S not covering v; reason: the two agree whenever θ + ξ is generic, which holds outside a null set of ties; expectations are unchanged
--   - encoding: ξ_v ∼ Unif[−1, 1] independent → xiLaw: 2^{−|V|} · Lebesgue measure on [−1, 1]^V; reason: the product of the uniform laws; a probability measure (sanity file)
--   - encoding: a finite graph G (the setting of Lemma 3.1, §3) → a finite simple graph (SimpleGraph on a Fintype V); reason: §4.1: all graphs in the main argument are finite, undirected and simple; a matching uses no loop and parallel copies of an edge cover the same vertices, so the covered-set statements do not change
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), §3.2, eq. (7), p.6 (PDF p.7); setting p.5 (PDF p.6)

import Mathlib
import Definitions.Def_StochMatchPoly_edgeLaw
import Definitions.Def_StochMatchPoly_perturbedCover

open Classical

namespace StochMatchPoly

/-- S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), §3.2, eq. (7), p.6 (PDF p.7), with the setting of §3.2, p.5 (PDF p.6).

"Let θ ∈ ℝ^V be deterministically fixed, and let ξ_v ∼ Unif[−1, 1] be chosen independently for
each vertex and also of ω. In G(ω) choose the (unique) matching M^θ maximizing the sum of
covered-vertex weights w_v = θ_v + ξ_v. Let X^θ_v := 1{v∈V(M^θ)} be the indicator that vertex v is
matched." … "Σ_{u,v} |Cov(X^θ_u, X^θ_v)| ≤ … ≤ 8 Σ_i E X^θ_i." (7)

**Formalization Note.** `G(ω)` is the random subgraph of the finite simple graph `G` with
independent edges of probabilities `q e ∈ [0, 1]` (the setting of Lemma 3.1, p.4). `X^θ_v` is
`coverIndicator`, which equals the coverage indicator of the unique `M^θ` outside a null set of
ties (see the definition's note). The covariance sum runs over ordered pairs and includes the
diagonal (§4.1). The constant `8` is the paper's. -/
theorem eq_7 {V : Type*} [Fintype V] (G : SimpleGraph V) (q : Sym2 V → ℝ)
    (hq : ∀ e ∈ G.edgeFinset, 0 ≤ q e ∧ q e ≤ 1) (θ : V → ℝ) :
    ∑ u, ∑ v, |covθ q G.edgeFinset θ u v| ≤ 8 * ∑ i, mθ q G.edgeFinset θ i := by sorry

end StochMatchPoly
