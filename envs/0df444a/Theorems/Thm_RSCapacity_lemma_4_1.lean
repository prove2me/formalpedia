-- Prove2me | Theorems.Thm_RSCapacity_lemma_4_1
-- name    : RSCapacity.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:34.437674+00:00
-- url     : https://prove2.me/theorems/fcb0103f-bb1c-40de-8d74-cef59bc647d9
-- title:
--   Lemma 4.1 (Degree properties of $\mathcal Q$)
-- statement:
--   Fix integers $1\le r<K\le A$, an integer $m\ge0$ and reals $1<c<s<A/(K-1)$, and let $\mathcal Q=\mathcal Q(A,K,r,m,c,s)$ and $B=\lceil mA/(K-1)\rceil$. Every $Q\in\mathcal Q$ satisfies
--   1. $\deg_{Y_j}Q\le B$ for every $j=0,\dots,r$;
--   2. $\deg_{(1,K-1,K-2,\dots,K-r-1)}Q<mA$;
--   3. for every $P\in F[X]$ with $\deg P<K$,
--   $$\deg_X Q(X,P,P^{[1]},\dots,P^{[r]})<mA .$$
--
--   The third bound is what turns $A$ roots of multiplicity $m$ into the vanishing of the differential substitution.
--
--   Differences from the source:
--   - encoding: a zero polynomial satisfies every displayed upper degree bound (p.10) → strict bounds use weightedTotalDegree' and Polynomial.degree, which are ⊥ at 0; reason: the paper's convention; no nonzero instance changes
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 4.1, p.13 (PDF 15)

import Mathlib
import Definitions.Def_RSCapacity_DiffSubst
import Definitions.Def_RSCapacity_InterpSpace

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-- **Lemma 4.1 (Degree properties).** Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 4.1, p.13
(PDF 15), under the standing hypotheses of §4.1 (1 ≤ r < K ≤ A integers, 1 < c < s < u = A/(K − 1)).
Every Q ∈ 𝒬 satisfies deg_{Y_j} Q ≤ B for every j; deg_{(1,K−1,…,K−r−1)} Q < mA; and for every P
with deg P < K, deg_X Q(X, P, P^{[1]}, …, P^{[r]}) < mA.

**Formalization Note.** Strict degree bounds use `weightedTotalDegree'` and `Polynomial.degree`
(both `⊥` at zero), so the zero polynomial satisfies them (p.10). -/
theorem lemma_4_1 {F : Type*} [Field F] (A K r m : ℕ) (c s : ℝ) (hr : 1 ≤ r) (hrK : r < K)
    (hKA : K ≤ A) (hc : 1 < c) (hcs : c < s) (hsu : s < (A : ℝ) / ((K : ℝ) - 1))
    (Q : MvPolynomial (Fin (r + 2)) F) (hQ : Q ∈ interpSpace F A K r m c s) :
    (∀ j : Fin (r + 1), Q.degreeOf j.succ ≤ Bdeg m A K) ∧
    Q.weightedTotalDegree' (diffWeight K r) < ((m * A : ℕ) : WithBot ℕ) ∧
    ∀ P : F[X], P.degree < K → (diffEval Q P).degree < ((m * A : ℕ) : WithBot ℕ) := by sorry

end RSCapacity
