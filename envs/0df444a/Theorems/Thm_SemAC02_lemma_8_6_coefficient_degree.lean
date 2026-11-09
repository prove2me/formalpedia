-- Prove2me | Theorems.Thm_SemAC02_lemma_8_6_coefficient_degree
-- name    : SemAC02.lemma_8_6_coefficient_degree
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:38.591802+00:00
-- url     : https://prove2.me/theorems/184d25eb-45fc-4b5d-8537-a288ddd6edef
-- title:
--   Lemma 8.6 — coefficient degree and locality
-- statement:
--   Let $g_0$ be antitone with $g_0(X)\wedge g_0(\overline X)=0$, $L$, $\Omega_0,\Omega_1$ as in Lemma 8.5, and $\Omega(z)=\prod_i\Omega_{z_i}$ for $z\in\{0,1\}^n$. For $u\in\mathcal B_v$ ($v=nm$) let $c_S(u)\in\mathcal B_n$, $S\in L^n$, be the unique functions of $z$ with
--   $$
--   u(X)=\sum_{S\in L^n}c_S(u)(z)\,x_S(X)\qquad\text{for every }X\in\Omega(z). \tag{46}
--   $$
--   Let $f\in\operatorname{span}\{x_T:T\in L^n\}$ and $p\in\mathcal B_v$. Then
--   $$
--   \deg c_S(fp)\le\deg p\qquad(S\in L^n),
--   $$
--   and if $p$ involves only blocks indexed by $J\subseteq[n]$, then $c_S(fp)$ depends only on $z_J$.
--
--   This controls the degree of the base-variable coefficients of a proof line by the degree of its multiplier, independently of $f$.
--
--   Differences from the source:
--   - generalization: g₀ = g, the gadget circuit of §8.1 → any antitone Boolean function g₀ with g₀(X) ∧ g₀(X̄) = 0; reason: the coordinates (46) and the proof use only antitonicity and disjointness; the gadget's evaluation is such a function
--   - encoding: the coordinates c_S(fp) defined by (46) → any family c satisfying the expansion identity for f·p on every fibre; reason: by Lemma 8.5 every fibre is nonempty (when L ≠ ∅) and the x_S form a basis on it, so the family is unique and equals the paper's c_S(fp); if L = ∅ there is no S
--   - encoding: deg of c_S(fp) ∈ B_n; deg p for p ∈ B_v; p involves only blocks J → a polynomial r over Fin n of totalDegree ≤ totalDegree p computing c_S(fp); p any polynomial; every variable (i, j) of p has i ∈ J; reason: degree in B_n is the least degree of a representative; for p multilinear this is the source's statement, and a non-multilinear p is a representative of larger total degree of the same element
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Lemma 8.6, p.65 (PDF p.67)

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_multiplierSpace

namespace SemAC02

open MvPolynomial

/-- **Lemma 8.6 (Coefficient degree and locality)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.6, p.65): let
`f ∈ span{x_T : T ∈ L^n}` and `p ∈ B_v`. Then `deg c_S(fp) ≤ deg p` for `S ∈ L^n`. If `p`
involves only blocks indexed by `J ⊆ [n]`, then `c_S(fp)` depends only on `z_J`.

Here (p.65) `Ω = (Ω₀ ∪ Ω₁)^n` with fibres `Ω(z) = ∏_i Ω_{z_i}`, and for `u ∈ B_v` the coordinates
`c_S(u) ∈ B_n` are the unique functions of `z` with `u(X) = ∑_{S∈L^n} c_S(u)(z) x_S(X)` for every
`X ∈ Ω(z)` (46).

**Formalization Note** Stated for every antitone `g₀` with `g₀(X) ∧ g₀(X̄) = 0` (the assumptions
of §8.1–8.2 that the coordinates use). The coordinates of `fp` are given as any family `c`
satisfying the expansion identity on every fibre; by Lemma 8.5 (every fibre is nonempty and the
`x_S` form a basis on it) such a family is unique, so it is the paper's `c_S(fp)`. The degree of a
function on `{0,1}^n` is the least total degree of a polynomial computing it; `deg p` is bounded
by the total degree of the polynomial `p`. "`p` involves only blocks `J`": every variable
`(i, j)` of `p` has `i ∈ J`. -/
theorem lemma_8_6_coefficient_degree {n m : ℕ} (g₀ : (Fin m → Bool) → Bool) (hanti : Antitone g₀)
    (hdisj : ∀ X : Fin m → Bool, ¬ (g₀ X = true ∧ g₀ (fun j => !X j) = true))
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g₀ n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (c : {A : Finset (Fin n × Fin m) // IsLnSupport g₀ A} → (Fin n → Bool) → ZMod 2)
    (hc : ∀ (z : Fin n → Bool) (X : Fin n × Fin m → Bool), InFiber g₀ z X →
      eval (toF2 X) (f * p) = ∑ S, c S z * eval (toF2 X) (AC02Frege.xMon S.1)) :
    (∀ S, ∃ r : MvPolynomial (Fin n) (ZMod 2), r.totalDegree ≤ p.totalDegree ∧
        ∀ z : Fin n → Bool, eval (toF2 z) r = c S z) ∧
    ∀ J : Finset (Fin n), (∀ v ∈ p.vars, v.1 ∈ J) →
      ∀ S (z z' : Fin n → Bool), (∀ i ∈ J, z i = z' i) → c S z = c S z' := by sorry

end SemAC02
