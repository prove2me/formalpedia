-- Prove2me | Theorems.Thm_SunGroupIso_Class2_lemma_5_12
-- name    : SunGroupIso.Class2.lemma_5_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:08:51.166212+00:00
-- url     : https://prove2.me/theorems/106445a3-178d-4faf-a539-58cecc3c1913
-- title:
--   Lemma 5.12 — matching extended vectors iff block-diagonal congruence of the constructed tuples with Q_5 = I
-- statement:
--   Let $(z,Y,g,F,\rho)$, $(z',X,g',E,\rho')$ be group restrictions of finite class-2 $p$-groups $G,H$ (same parameters) satisfying the standing assumptions of Section 5, including nontrivial specified central cyclic factors, let $\vec a$, $\vec b$ be extended vectors of them and $A$, $B$ their Matrix Tuple Constructions. If $\rho(a_i)=\rho'(b_i)$ for $1\le i\le\psi+\zeta_0+\eta$, then the restriction of $\vec a$ has an extended vector $\vec v$ matching $\vec b$ if and only if there is an invertible block-diagonal $Q=\mathrm{diag}(Q_1,\dots,Q_5)$ with $Q_5=I$ and $Q^TA_sQ=B_s$ for every matrix of the tuples (the tuples having the same block sizes).
--
--   Differences from the source:
--   - reading: the standing assumptions of Section 5 ('we may assume', pp. 13–14; (7), p. 31; τ ≥ 2 in the proof of Lemma 5.15); reindexing with all remaining z_i of order p (PDF 29) → hypothesis Sec5Standing r r' (ψ, η equal, Y ≅ X, quotients isomorphic, ord(z_i) = ord(z'_i), ord(g̃_i) = ord(g̃'_i), equal z-coefficients of [g_i,g_j] and g_i^{ord(g̃_i)} for i, j ≤ γ, τ ≥ 2); p ≤ ord(z_i); reason: these are source standing assumptions; the positive cyclic orders prevent a zero denominator ord(z_i)/p
--   - reading: two group restrictions (Problem 4.3) → two restrictions with the same parameters ζ, γ, κ, τ, δ; reason: restriction isomorphism compares z_i with z'_i, g_i with g'_i and ρ with ρ' coordinatewise, and condition 1 of p. 13 assumes the parameters equal
--   - encoding: matrix tuples A, B ∈ M(m,R)^s → MatTuple (block-size list and one-based entry functions); BlockCongruent requires equal block sizes and a list-wise congruence; reason: tuples of different sizes are never congruent; the representation changes no instance
--   - encoding: ρ : F → R^κ → ρ : G → Fin κ → ZMod (p^τ), only its values on F used by any condition or code; reason: a function on F is the restriction of a function on G; values off F are never read
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 5.12, p. 35 (PDF p. 37)

import Mathlib
import Definitions.Def_SunGroupIso_Class2_MatrixTuple

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Lemma 5.12** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 5.12, p. 35, PDF p. 37). Let `a⃗, b⃗` be extended vectors of two group
restrictions (under the standing assumptions of Section 5) and `A, B` the matrix tuples constructed for them.
If `ρ(a_i) = ρ'(b_i)` for `1 ≤ i ≤ ψ + ζ_0 + η`, then the group restriction of `a⃗` has an extended vector `v⃗`
matching `b⃗` if and only if an invertible block-diagonal `Q` with `Q_5 = I` has `Qᵀ A Q = B`. -/
theorem lemma_5_12 {p : ℕ} (hp : p.Prime) {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (hG : IsPGroupClass2 p G) (hH : IsPGroupClass2 p H) {ζ γ κ τ δ : ℕ}
    (r : Restriction G p ζ γ κ τ) (r' : Restriction H p ζ γ κ τ)
    (hr : IsRestriction p δ r) (hr' : IsRestriction p δ r') (hstd : Sec5Standing r r')
    {n n' : ℕ} (a : Fin n → G) (b : Fin n' → H) (ha : IsExtVec r a) (hb : IsExtVec r' b)
    (hρ : ∀ i, 1 ≤ i → i ≤ r.psi + r.zeta0 + r.eta → r.ρ (at1 a i) = r'.ρ (at1 b i)) :
    (∃ v : Fin n → G, IsExtVec r v ∧ Matches r v r' b) ↔ BlockCongruent (mtc r a) (mtc r' b) := by sorry

end SunGroupIso.Class2
