-- Prove2me | Theorems.Thm_SetMultCost_observation_3_2
-- name    : SetMultCost.observation_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:06.6811+00:00
-- url     : https://prove2.me/theorems/8fb77068-179c-4806-b746-fc90bb7fc591
-- title:
--   Observation 3.2 — Binet–Minc in characteristic $p$
-- statement:
--   In characteristic $p$, for every $S$ with $|S|>p$, the coefficient $(|S|-1)!$ in (1.6) vanishes. Hence
--
--   $$\mathrm{RPerm}_{d,n}(X)=\sum_{\substack{\lambda\in\mathcal P(d)\\S\in\lambda\implies|S|\le p}}(-1)^{d-|\lambda|}\prod_{S\in\lambda}(|S|-1)!\sum_{j=1}^n\prod_{i\in S}x_{i,j}.\tag{3.3}$$
--
--   So the bottom product gates of this expression have fan-in at most $p$, the structural feature behind the whole mission.
--
--   Differences from the source:
--   - generalization: a field F of characteristic p, with a symbolic matrix → any commutative ring of characteristic p, with any matrix; reason: the symbolic matrix has entries in the polynomial ring over F, which has characteristic p and is an instance
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Observation 3.2, p.12

import Mathlib
import Definitions.Def_SetMultCost_RPerm

open scoped Classical

namespace SetMultCost

/-- **Observation 3.2.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.12: "Fix a field F with char(F) = p. Then in Equation (1.6), for
every S with |S| > p, the corresponding coefficient (|S| − 1)! is 0 mod p. This implies over F,
Equation (1.6) simplifies to: RPermd,n(X) = ∑_{λ∈P(d), S∈λ ⟹ |S|≤p} (−1)^{d−|λ|} ∏_{S∈λ} (|S| −
1)! ∑_{j=1}^n ∏_{i∈S} xi,j. (3.3)".

**Formalization Note.** Over any commutative ring of characteristic `p`, since the statement is about
the symbolic matrix, whose entries lie in `MvPolynomial _ F`, not a field. -/
theorem observation_3_2 {R : Type*} [CommRing R] (p : ℕ) (hp : p.Prime) [CharP R p] {d n : ℕ}
    (hdn : d ≤ n) (X : Matrix (Fin d) (Fin n) R) :
    (∀ S : Finset (Fin d), p < S.card → ((S.card - 1).factorial : R) = 0) ∧
    RPerm X = ∑ lam ∈ (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin d)))).filter
        (fun lam => ∀ S ∈ lam.parts, S.card ≤ p), binetMincTerm X lam := by sorry

end SetMultCost
