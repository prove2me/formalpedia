-- Prove2me | Theorems.Thm_ProxGapTight_lemma_3_4_shortenings
-- name    : ProxGapTight.lemma_3_4_shortenings
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:57:06.830843+00:00
-- url     : https://prove2.me/theorems/28b4bdd7-d037-44f6-ab32-64791af40998
-- title:
--   Lemma 3.4 — shortenings of $U_m$ and $d(U_m)=e_m$
-- statement:
--   Let $p$ be a prime and $Q=p^a$ with $Q>32$, $Q\notin\{49,121\}$, and let $X$ be the set of lines of $\mathbb F_Q^m$. For every sufficiently large $m$ and every $S\subseteq X$:
--
--   1. **Two-incidence-vector containment.** If $|S|\le L_m$, then the shortening $U_m[S]$ is contained in the span of two incidence vectors $u_W,u_{W'}$.
--   2. **One-incidence-vector containment.** If $|S|\le 4e_m/3$, then $U_m[S]$ is contained in the span of one incidence vector $u_W$.
--   3. **Minimum distance.** $d(U_m)=e_m$.
--
--   Item 2 is what makes the counterexample words far from the code: every word of weight at most $4e_m/3$ in the extended code is a multiple of a single incidence vector.
--
--   **Formalization Note** $\mathbb F_Q$ is any field of order $p^a$; "sufficiently large $m$" is a threshold $m_0$ depending only on $p$ and $a$.
--
--   Differences from the source:
--   - generalization: F_Q → any field with Fintype.card = p ^ a; reason: all fields of that order are isomorphic to it; the statement specializes to it
--   - encoding: |S| ≤ 4e_m/3 → 3 * S.card ≤ 4 * em (p ^ a) m; reason: equivalent over the integers
--   - encoding: for every sufficiently large m → ∃ m₀ (depending on p, a) ∀ m ≥ m₀, placed before the field K; reason: the stated dependency
--   - encoding: U_m[S] contained in the span of two incidence vectors → ∃ W W' : Codim2 K m with shorten (Um K m p) S ≤ span {u_W, u_{W'}}, W = W' allowed; reason: the span of one incidence vector lies in the span of two (there are at least two codimension-two subspaces for m ≥ 3), so the condition is the same
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), Lemma 3.4, p.8 (proof pp.8–9; context Lemma 3.2, p.7)

import Mathlib
import Definitions.Def_ProxGapTight_Um
import Definitions.Def_ProxGapTight_shorten
import Definitions.Def_ProxGapTight_minDist
import Definitions.Def_ProxGapTight_em
import Definitions.Def_ProxGapTight_Lm

namespace ProxGapTight

/-- **Lemma 3.4**, Kominers, Thaler, Zheng, manuscript (Sept. 2026), p.8 (proof pp.8–9). For every
sufficiently large `m` and every `S ⊆ X`:
1. if `|S| ≤ L_m`, then `U_m[S]` is contained in the span of two incidence vectors;
2. if `|S| ≤ 4e_m/3`, then `U_m[S]` is contained in the span of one incidence vector;
3. `d(U_m) = e_m`.

**Formalization Note.** Standing context of §3.1 (p.7): `p` prime, `Q = p^a > 32`,
`Q ∉ {49, 121}`; "sufficiently large `m`" is `∃ m₀` depending on `p, a`. `F_Q` is any field `K` of
order `p^a`, `F_p = ZMod p`, `X = Lines K m`. `|S| ≤ 4e_m/3` is written `3|S| ≤ 4e_m`. -/
theorem lemma_3_4_shortenings (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = p ^ a →
      (∀ S : Finset (Lines K m), S.card ≤ Lm (p ^ a) m →
        ∃ W W' : Codim2 K m, shorten (Um K m p) S ≤
          Submodule.span (ZMod p) {incVec (ZMod p) W, incVec (ZMod p) W'}) ∧
      (∀ S : Finset (Lines K m), 3 * S.card ≤ 4 * em (p ^ a) m →
        ∃ W : Codim2 K m, shorten (Um K m p) S ≤ Submodule.span (ZMod p) {incVec (ZMod p) W}) ∧
      minDist (Um K m p) = em (p ^ a) m := by sorry

end ProxGapTight
