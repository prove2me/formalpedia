-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_lemma_5_5
-- name    : RSBeyondJohnson.FirstOrder.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:48.010202+00:00
-- url     : https://prove2.me/theorems/f127e1d8-9b99-43b0-992e-8c822b4961fa
-- title:
--   Lemma 5.5 — squarefree first-order counting
-- statement:
--   Let $1\le D\le n-2$, $D+1\le A\le n$, $B\ge1$, $1\le M\le B$, $H\ge0$, distinct $\alpha_1,\dots,\alpha_n\in F$, a received curve $w(Z)=\sum_{t=0}^\ell Z^tw_t$ with $\ell\ge1$, and the parameters $\lambda_{\mathrm{agr}},\tau,u,v,F_{\mathrm{reg}},S,H_s,J_\ell$ of (43); assume characteristic zero or $p>\max\{D,M\}$.
--   (1) Let $Q\in F[X,Z,Y_0,Y_1]$ be nonzero, of total jet degree at most $B$, $Y_1$-degree at most $M$, challenge degree at most $H$. For each integer $D+1\le L\le A$, outside a set of at most
--   $$\min_{D+1\le L_0\le A}E^{(\ell)}_{\mathrm{ord}}(D,A,n;S,H_s;L_0)+\frac{n-L+1}{A-L+1}\lambda_{\mathrm{agr}}J_\ell+\ell(n-L)\frac{n-D}{L-D}F_{\mathrm{reg}}\qquad(44)$$
--   challenges, every degree-$\le D$ solution of $Q(X,z,P,P^{[1]})=0$ with at least $A$ agreements has the full common-witness property with message dimension $D+1$.
--   (2) For a nonzero fixed-word equation with the same jet-degree bounds, the number of close solutions is at most
--   $$\lambda_{\mathrm{agr}}F_{\mathrm{reg}}+S\le4\lambda_{\mathrm{agr}}DBM+2BM+B.\qquad(45)$$
--
--   Differences from the source:
--   - encoding: positions 1, …, n; distinct evaluation points α_1, …, α_n → Fin n (0-based); α : Fin n → F with Function.Injective α; reason: Lean indexing; the same instances
--   - encoding: outside a set of at most min_{L₀}(…) + (rest) → ∃ E : Finset F with |E| ≤ E_ord(…; L₀) + (rest) for every D + 1 ≤ L₀ ≤ A; reason: a bound for every L₀ by one set is a bound by the minimum
--   - encoding: Q ∈ F[X, Z, Y₀, Y₁] and its degrees; Q(X, z, P, P^[1]) → (MvPolynomial (Option (Fin 2)) F)[X]; jetDegree, degreeOf (some 1) of every Z-coefficient, natDegree; hasseJetEval 1 (specZ Q z) P; reason: same objects
--   - encoding: the number of close solutions of a fixed-word equation → the set {P : deg ≤ D, Q(X, P, P^[1]) = 0, ≥ A agreements with y} is Finite and its ncard is bounded, for every word y; reason: ncard of an infinite set is 0
--   - encoding: 1 ≤ D ≤ n − 2; (43) integer parameters → 1 ≤ D, D + 2 ≤ n; τ, u, v, F_reg, S, H_s, J_ℓ in ℤ; reason: avoids natural subtraction
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 33, Lemma 5.5 (with the parameters (43))

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement
import Definitions.Def_RSBeyondJohnson_FirstOrder_Interpolation
import Definitions.Def_RSBeyondJohnson_FirstOrder_Counting

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Lemma 5.5 (Squarefree first-order counting)**, p. 33, with the standing parameters of §5.3:
`1 ≤ D ≤ n − 2`, `D + 1 ≤ A ≤ n`, `B ≥ 1`, `1 ≤ M ≤ B`, `H ≥ 0`, distinct `α_i ∈ F`, a received
curve `w(Z) = ∑_{t=0}^{ℓ} Z^t w_t` with `ℓ ≥ 1`, and `λ_agr, τ, u, v, F_reg, S, H_s, J_ℓ` of (43);
characteristic zero or `p > max{D, M}`.
(1) For every nonzero `Q ∈ F[X, Z, Y₀, Y₁]` of total jet degree `≤ B`, `Y₁`-degree `≤ M` and
challenge degree `≤ H`, and every integer `D + 1 ≤ L ≤ A`, there is one set `E ⊆ F` with
`|E| ≤ min_{D+1 ≤ L₀ ≤ A} E^(ℓ)_ord(D, A, n; S, H_s; L₀) + ((n − L + 1)/(A − L + 1)) λ_agr J_ℓ
+ ℓ(n − L)((n − D)/(L − D)) F_reg` (44) (encoded as: `|E|` is at most the right side for every
such `L₀`) outside which every degree-`≤ D` solution of `Q(X, z, P, P^[1]) = 0` with at least `A`
agreements has the full common-witness property with message dimension `D + 1`.
(2) For a nonzero fixed-word equation `Q ∈ F[X, Y₀, Y₁]` with the same jet-degree bounds and
every word `y`, the close solutions (degree `≤ D`, at least `A` agreements) are finitely many,
at most `λ_agr F_reg + S`, and `λ_agr F_reg + S ≤ 4λ_agr D B M + 2BM + B` (45). -/
theorem lemma_5_5 {F : Type*} [Field F] {n ℓ : ℕ} (D A B M H : ℕ) (hD : 1 ≤ D)
    (hDn : D + 2 ≤ n) (hDA : D + 1 ≤ A) (hAn : A ≤ n) (hB : 1 ≤ B) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hℓ : 1 ≤ ℓ) (α : Fin n → F) (hα : Function.Injective α) (w : Fin (ℓ + 1) → Fin n → F)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    (∀ Q : (MvPolynomial (Option (Fin 2)) F)[X], Q ≠ 0 →
      (∀ j, jetDegree (Q.coeff j) ≤ B) → (∀ j, (Q.coeff j).degreeOf (some 1) ≤ M) →
      Q.natDegree ≤ H →
      ∀ L : ℕ, D + 1 ≤ L → L ≤ A →
        ∃ E : Finset F,
          (∀ L₀ : ℕ, D + 1 ≤ L₀ → L₀ ≤ A →
            (E.card : ℝ) ≤ eOrd ℓ D A n (sOrd B M : ℝ) (hOrd M H : ℝ) L₀ +
              ((n : ℝ) - L + 1) / ((A : ℝ) - L + 1) * lamAgr n D A * (jReg ℓ D B M H : ℝ) +
              (ℓ : ℝ) * ((n : ℝ) - L) * (((n : ℝ) - D) / ((L : ℝ) - D)) * (fReg D B M : ℝ)) ∧
          ∀ z : F, z ∉ E → ∀ P : F[X], P.natDegree ≤ D →
            RSListDecodingCapacity.AllRates.hasseJetEval 1 (specZ Q z) P = 0 →
            A ≤ (agrSet α w z P).card → HasFullCommonWitness (D + 1) α w z P) ∧
    (∀ Q : MvPolynomial (Option (Fin 2)) F, Q ≠ 0 → jetDegree Q ≤ B →
      Q.degreeOf (some 1) ≤ M → ∀ y : Fin n → F,
        {P : F[X] | P.natDegree ≤ D ∧ RSListDecodingCapacity.AllRates.hasseJetEval 1 Q P = 0 ∧
          A ≤ RSListDecodingCapacity.AllRates.agreement α y P}.Finite ∧
        ({P : F[X] | P.natDegree ≤ D ∧ RSListDecodingCapacity.AllRates.hasseJetEval 1 Q P = 0 ∧
          A ≤ RSListDecodingCapacity.AllRates.agreement α y P}.ncard : ℝ) ≤
          lamAgr n D A * (fReg D B M : ℝ) + (sOrd B M : ℝ) ∧
        lamAgr n D A * (fReg D B M : ℝ) + (sOrd B M : ℝ) ≤
          4 * lamAgr n D A * D * B * M + 2 * B * M + B) := by sorry

end RSBeyondJohnson.FirstOrder
