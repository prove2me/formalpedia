-- Prove2me | Theorems.Thm_StochMatchPoly_eq_14
-- name    : StochMatchPoly.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:32:31.793609+00:00
-- url     : https://prove2.me/theorems/df18ef55-59d4-40dc-8541-e73b7256b5e0
-- title:
--   Eq. (14) — the potential changes by at most $h(m_v(\theta')-s_v)$
-- statement:
--   In the setting of §3.2–3.3, let $\theta'$ agree with $\theta$ except that $\theta'_v=\theta_v+h$, where $h$ is any real number, and let $\Psi(\theta)=F(\theta)-\sum_u\theta_us_u$ be the potential (10) for a target vector $s$. Then
--
--   $$\Psi(\theta')-\Psi(\theta)\le h\bigl(m_v(\theta')-s_v\bigr),$$
--
--   for either sign of $h$.
--
--   Together with (12) this shows that every calibration update of Lemma 3.3 decreases the potential by at least $h^2/2$.
--
--   Differences from the source:
--   - encoding: X^θ_v = 1{v ∈ V(M^θ)} for the matching M^θ maximizing the covered-vertex weight, unique almost surely → coverIndicator S (θ + ξ) v = 1 iff some matching of S covering v scores strictly more than every matching of S not covering v; reason: the two agree whenever θ + ξ is generic, which holds outside a null set of ties; expectations are unchanged
--   - generalization: s_v = E X_v, the marginals of a randomized matching algorithm A (§3.3) → s an arbitrary real vector; reason: the derivation of (14) uses no property of s (the s-term of Ψ is linear); it specializes to the paper's s
--   - encoding: a finite graph G (the setting of Lemma 3.1, §3) → a finite simple graph (SimpleGraph on a Fintype V); reason: §4.1: all graphs in the main argument are finite, undirected and simple; a matching uses no loop and parallel copies of an edge cover the same vertices, so the covered-set statements do not change
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), §3.3, eq. (14), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_StochMatchPoly_edgeLaw
import Definitions.Def_StochMatchPoly_perturbedCover

open Classical

namespace StochMatchPoly

/-- S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), §3.3, eq. (14), p.8 (PDF p.9).

"Let θ′ agree with θ except that θ′_v = θ_v + h, where h is any real number." … "Taking
expectations, and subtracting the change hs_v in the target term of the potential, gives
Ψ(θ′) − Ψ(θ) ≤ h(m_v(θ′) − s_v). (14) Note that the inequality holds for either sign of h."

**Formalization Note.** `θ′ = Function.update θ v (θ v + h)`, `h` any real. `Ψ` is the potential
(10) for the target vector `s`; the derivation of (14) uses no property of `s`, so `s` is an
arbitrary real vector here (in §3.3 it is the marginal vector of a randomized matching
algorithm). -/
theorem eq_14 {V : Type*} [Fintype V] (G : SimpleGraph V) (q : Sym2 V → ℝ)
    (hq : ∀ e ∈ G.edgeFinset, 0 ≤ q e ∧ q e ≤ 1) (s θ : V → ℝ) (v : V) (h : ℝ) :
    Ψ q G.edgeFinset s (Function.update θ v (θ v + h)) - Ψ q G.edgeFinset s θ ≤
      h * (mθ q G.edgeFinset (Function.update θ v (θ v + h)) v - s v) := by sorry

end StochMatchPoly
