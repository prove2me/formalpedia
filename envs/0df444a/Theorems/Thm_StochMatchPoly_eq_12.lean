-- Prove2me | Theorems.Thm_StochMatchPoly_eq_12
-- name    : StochMatchPoly.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:29:35.189187+00:00
-- url     : https://prove2.me/theorems/9cd71b19-455f-4885-948b-7c0b7eab07ce
-- title:
--   Eq. (12) — shifting one offset by $h$ moves that vertex's marginal by at most $|h|/2$
-- statement:
--   In the setting of §3.2–3.3 (random subgraph with independent edges of probabilities $q_e\in[0,1]$, independent perturbations $\xi_v\sim\mathrm{Unif}[-1,1]$), let $\theta'$ agree with $\theta$ except that $\theta'_v=\theta_v+h$, where $h$ is any real number. Then
--
--   $$|m_v(\theta')-m_v(\theta)|\le\frac{|h|}{2}.$$
--
--   The bound says the coverage probability of $v$ is $\tfrac12$-Lipschitz in its own offset; it drives the potential decrease in Lemma 3.3.
--
--   Differences from the source:
--   - encoding: X^θ_v = 1{v ∈ V(M^θ)} for the matching M^θ maximizing the covered-vertex weight, unique almost surely → coverIndicator S (θ + ξ) v = 1 iff some matching of S covering v scores strictly more than every matching of S not covering v; reason: the two agree whenever θ + ξ is generic, which holds outside a null set of ties; expectations are unchanged
--   - encoding: a finite graph G (the setting of Lemma 3.1, §3) → a finite simple graph (SimpleGraph on a Fintype V); reason: §4.1: all graphs in the main argument are finite, undirected and simple; a matching uses no loop and parallel copies of an edge cover the same vertices, so the covered-set statements do not change
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), §3.3, eq. (12), p.8 (PDF pp.8–9)

import Mathlib
import Definitions.Def_StochMatchPoly_edgeLaw
import Definitions.Def_StochMatchPoly_perturbedCover

open Classical

namespace StochMatchPoly

/-- S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), §3.3, eq. (12), p.8 (PDF pp.8–9).

"Let θ′ agree with θ except that θ′_v = θ_v + h, where h is any real number. … Averaging over the
conditioning gives |m_v(θ′) − m_v(θ)| ≤ |h|/2." (12)

**Formalization Note.** `θ′ = Function.update θ v (θ v + h)`. `m_v(θ)` is `mθ`, the marginal of
`X^θ_v` under independent edges with probabilities `q e ∈ [0, 1]` and the independent uniform
perturbation `ξ ∼ Unif[−1, 1]^V` (§3.2–3.3 setting). -/
theorem eq_12 {V : Type*} [Fintype V] (G : SimpleGraph V) (q : Sym2 V → ℝ)
    (hq : ∀ e ∈ G.edgeFinset, 0 ≤ q e ∧ q e ≤ 1) (θ : V → ℝ) (v : V) (h : ℝ) :
    |mθ q G.edgeFinset (Function.update θ v (θ v + h)) v - mθ q G.edgeFinset θ v| ≤
      |h| / 2 := by sorry

end StochMatchPoly
