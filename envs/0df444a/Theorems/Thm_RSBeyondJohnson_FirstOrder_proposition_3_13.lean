-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_proposition_3_13
-- name    : RSBeyondJohnson.FirstOrder.proposition_3_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:28.04903+00:00
-- url     : https://prove2.me/theorems/7abcf397-12ce-47d1-a461-48c5ca426955
-- title:
--   Proposition 3.13 — constructing a symbolic explainer
-- statement:
--   Fix integers $d\ge0$, $m\ge1$, $K\ge1$, $1\le A\le n$. Let $\mathcal Q\subseteq F[X,Y_0,\dots,Y_d]$ be the span of a finite set of monomials, invariant under translations in $X$ and $Y_0$, whose members have total degree at most $B_{\mathrm{jet}}$ in $Y_0,\dots,Y_d$ and specialize at every polynomial of degree $<K$ to degree $<mA$. Let $R_{\mathrm{loc}}$ bound the rank of the local constraint map $\Phi^{d,m}_{0,0}$ on $\mathcal Q$, and suppose $N_{\mathrm{coef}}=\dim\mathcal Q>nR_{\mathrm{loc}}$. Then for distinct $\alpha_i\in F$ and $f,g\in F^n$ there is $Q\in F[Z]\otimes_F\mathcal Q$ with
--   $$\deg_ZQ\le\Big\lfloor\frac{nR_{\mathrm{loc}}B_{\mathrm{jet}}}{N_{\mathrm{coef}}-nR_{\mathrm{loc}}}\Big\rfloor,\qquad Q(X,z,Y)\ne0\ \text{for every }z,$$
--   and every polynomial $P$ of degree $<K$ agreeing with $f+zg$ in at least $A$ positions satisfies $Q(X,z,P,P^{[1]},\dots,P^{[d]})=0$ (17). For a received curve $w(Z)=\sum_{t=0}^\ell Z^tw_t$ ($\ell\ge1$) the same holds with $f+zg$ replaced by $w(z)$ and $\deg_ZQ\le\lfloor\ell nR_{\mathrm{loc}}B_{\mathrm{jet}}/(N_{\mathrm{coef}}-nR_{\mathrm{loc}})\rfloor$ (18). These assertions hold after any extension $L$ of the base field: the same $Q$ is nonzero at every $z\in L$ and satisfies (17)/(18) for every $z\in L$ and every $P\in L[X]$.
--
--   Differences from the source:
--   - encoding: positions 1, …, n; distinct evaluation points α_1, …, α_n → Fin n (0-based); α : Fin n → F with Function.Injective α; reason: Lean indexing; the same instances
--   - encoding: a finite monomial space 𝒬 → 𝒬 = MvPolynomial.restrictSupport F S for a Finset S of exponent vectors; reason: the span of finitely many monomials
--   - encoding: Q ∈ F[Z] ⊗_F 𝒬; deg_Z; Q(X, z, Y) → a polynomial in Z over F[X, Y] with every Z-coefficient in 𝒬; natDegree; specZ Q z = Q.eval (C z); reason: same object
--   - reading: These assertions hold after any extension of the base field → one Q over F works for every extension L : Type u: nonzero at every z ∈ L and (17)/(18) for z ∈ L, P ∈ L[X]; the case L = F is the base statement; reason: the stronger of the two readings (the proof keeps the same Q: its kernel vector is primitive and the constraints are polynomial identities over F[Z])
--   - encoding: ⌊nR_loc B_jet/(N_coef − nR_loc)⌋ → natural division n * Rloc * Bjet / (finrank 𝒬 − n * Rloc); reason: floor of a nonnegative rational; the denominator is positive by hypothesis
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 20, Proposition 3.13

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement
import Definitions.Def_RSBeyondJohnson_FirstOrder_Interpolation

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Proposition 3.13 (Constructing a symbolic explainer)**, p. 20. Let `𝒬 ⊆ F[X, Y₀, …, Y_d]`
be the span of a finite set `S` of monomials, invariant under translations in `X` and `Y₀`, whose
members have total degree at most `B_jet` in `Y₀, …, Y_d` and specialize at every polynomial of
degree `< K` to degree `< mA`, and let `R_loc` bound the rank of `Φ^{d,m}_{0,0}` on `𝒬`, with
`N_coef = dim 𝒬 > n R_loc`. For distinct `α_i` and `f, g ∈ F^n` there is `Q ∈ F[Z] ⊗_F 𝒬` with
`deg_Z Q ≤ ⌊n R_loc B_jet/(N_coef − n R_loc)⌋`, `Q(X, z, Y) ≠ 0` for every `z`, and (17) for every
degree-`< K` `P` agreeing with `f + z g` in at least `A` positions; for a received curve of
degree `ℓ` the same holds with `deg_Z Q ≤ ⌊ℓ n R_loc B_jet/(N_coef − n R_loc)⌋` (18). The
assertions hold after any extension `L` of the base field: the same `Q`, with challenges
`z ∈ L` and candidates `P ∈ L[X]`. -/
theorem proposition_3_13.{u} {F : Type u} [Field F] {n : ℕ} (d m K A : ℕ) (hm : 1 ≤ m)
    (hK : 1 ≤ K) (hA1 : 1 ≤ A) (hAn : A ≤ n)
    (S : Finset (Option (Fin (d + 1)) →₀ ℕ))
    (𝒬 : Submodule F (MvPolynomial (Option (Fin (d + 1))) F))
    (h𝒬 : 𝒬 = MvPolynomial.restrictSupport F (S : Set (Option (Fin (d + 1)) →₀ ℕ)))
    (htrans : ∀ a b : F, ∀ Q ∈ 𝒬, translateXY0 d a b Q ∈ 𝒬)
    (Bjet : ℕ) (hjet : ∀ Q ∈ 𝒬, jetDegree Q ≤ Bjet)
    (hspec : ∀ Q ∈ 𝒬, ∀ P : F[X], P.degree < (K : WithBot ℕ) →
      (RSListDecodingCapacity.AllRates.hasseJetEval d Q P).degree < ((m * A : ℕ) : WithBot ℕ))
    (Rloc : ℕ)
    (hRloc : Module.finrank F (LinearMap.range ((localConstraintMap d m (0 : F) 0).domRestrict 𝒬))
      ≤ Rloc)
    (hN : n * Rloc < Module.finrank F 𝒬)
    (α : Fin n → F) (hα : Function.Injective α) :
    (∀ f g : Fin n → F, ∃ Q : (MvPolynomial (Option (Fin (d + 1))) F)[X],
      (∀ j, Q.coeff j ∈ 𝒬) ∧
      Q.natDegree ≤ n * Rloc * Bjet / (Module.finrank F 𝒬 - n * Rloc) ∧
      ∀ (L : Type u) [Field L] [Algebra F L] (z : L),
        specZ (Q.map (MvPolynomial.map (algebraMap F L))) z ≠ 0 ∧
        ∀ P : L[X], P.degree < (K : WithBot ℕ) →
          A ≤ (agrSet (fun i => algebraMap F L (α i))
            (fun t i => algebraMap F L (lineCurve f g t i)) z P).card →
          RSListDecodingCapacity.AllRates.hasseJetEval d
            (specZ (Q.map (MvPolynomial.map (algebraMap F L))) z) P = 0) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ w : Fin (ℓ + 1) → Fin n → F,
      ∃ Q : (MvPolynomial (Option (Fin (d + 1))) F)[X],
      (∀ j, Q.coeff j ∈ 𝒬) ∧
      Q.natDegree ≤ ℓ * n * Rloc * Bjet / (Module.finrank F 𝒬 - n * Rloc) ∧
      ∀ (L : Type u) [Field L] [Algebra F L] (z : L),
        specZ (Q.map (MvPolynomial.map (algebraMap F L))) z ≠ 0 ∧
        ∀ P : L[X], P.degree < (K : WithBot ℕ) →
          A ≤ (agrSet (fun i => algebraMap F L (α i))
            (fun t i => algebraMap F L (w t i)) z P).card →
          RSListDecodingCapacity.AllRates.hasseJetEval d
            (specZ (Q.map (MvPolynomial.map (algebraMap F L))) z) P = 0) := by sorry

end RSBeyondJohnson.FirstOrder
