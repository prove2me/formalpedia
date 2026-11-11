-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_lemma_3_7
-- name    : RSBeyondJohnson.FirstOrder.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:24.758326+00:00
-- url     : https://prove2.me/theorems/77fa5e01-ba77-4a0b-abc5-ec5d5cbbf029
-- title:
--   Lemma 3.7 — local multiplicity: an agreement plus the constraints (11) give a root of multiplicity m
-- statement:
--   Fix an order $d\ge0$, a multiplicity $m\ge1$ and a received pair $(\alpha,y)\in F^2$. Let $Q\in F[X,Y_0,\dots,Y_d]$ satisfy the local hidden-derivative constraints $\Phi^{d,m}_{\alpha,y}(Q)=0$ of Definition 3.6. If a polynomial $P\in F[X]$ agrees with the received pair, $P(\alpha)=y$, then
--   $$Q\big(\alpha+T,\,P(\alpha+T),\,P^{[1]}(\alpha+T),\dots,P^{[d]}(\alpha+T)\big)\equiv0\pmod{T^m}.$$
--   Thus each agreement gives a root of multiplicity at least $m$ after substituting the candidate and its Hasse derivatives into $Q$; this holds in every characteristic. It is the local step of every interpolation argument in the paper.
--
--   Differences from the source:
--   - encoding: congruence (12) modulo T^m in F[T] → X^m divides (hasseJetEval d Q P).comp (X + C α), i.e. T is the polynomial variable; reason: Q(α + T, P(α + T), …) is Q(X, P, P^[1], …) composed with X ↦ α + T
--   - encoding: Q satisfies (11) → localConstraintMap d m α y Q = 0 (coefficients of T^0, …, T^{m−1} of the substitution (10)); reason: the image in F[T, V, Y]/(T^m) is zero exactly when these coefficients vanish
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 18, Lemma 3.7

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Interpolation

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Lemma 3.7 (Local multiplicity)**, p. 18. If `P(α) = y` and `Q` satisfies the order-`d`,
multiplicity-`m` local constraints (11) at `(α, y)`, then
`Q(α + T, P(α + T), P^[1](α + T), …, P^[d](α + T)) ≡ 0 (mod T^m)`. -/
theorem lemma_3_7 {F : Type*} [Field F] (d m : ℕ) (hm : 1 ≤ m) (α y : F)
    (Q : MvPolynomial (Option (Fin (d + 1))) F) (P : F[X]) (hP : P.eval α = y)
    (hQ : localConstraintMap d m α y Q = 0) :
    (X : F[X]) ^ m ∣ (RSListDecodingCapacity.AllRates.hasseJetEval d Q P).comp (X + C α) := by sorry

end RSBeyondJohnson.FirstOrder
