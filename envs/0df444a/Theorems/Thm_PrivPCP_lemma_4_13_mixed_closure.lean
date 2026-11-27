-- Prove2me | Theorems.Thm_PrivPCP_lemma_4_13_mixed_closure
-- name    : PrivPCP.lemma_4_13_mixed_closure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T03:34:56.411231+00:00
-- url     : https://prove2.me/theorems/bbd83ddf-d65c-553b-9a16-79dc485a4b10
-- title:
--   Lemma 4.13, main step over $\overline{\mathbb F}_q$: mixed irreducible factors of $E$ divide $P$
-- statement:
--   This is the main step of the proof of Lemma 4.13 in the source, stated over $K=\overline{\mathbb F}_q$, which is where the source works ("We work first over $K$").
--
--   There is an absolute constant $c_0>0$ such that the following holds. Let $q$ be prime, let $S_1,S_2\le\mathbb F_q^\times$ be subgroups of coprime orders $n_1,n_2$, and fix integers $0\le k_i<n_i$. Put $N=n_1n_2$ and $h=\min\{n_1-k_1,n_2-k_2\}$. Let $E,P\in K[X,Y]$ with $E\neq0$, $e_X=\deg_XE$, $e_Y=\deg_YE$ and $t=\max\{e_X,e_Y\}$. Suppose
--
--   $$t\le c_0\frac{h^3}{N},\qquad \deg_XP<k_1+e_X,\qquad \deg_YP<k_2+e_Y,$$
--
--   and that for every $\alpha\in S_1$ and $\beta\in S_2$ there are polynomials $R_\alpha(Y)$, $C_\beta(X)$ over $K$ with
--
--   $$P(\alpha,Y)=E(\alpha,Y)R_\alpha(Y),\qquad P(X,\beta)=E(X,\beta)C_\beta(X).$$
--
--   If $F\in K[X,Y]$ is irreducible, $F\mid E$, $\deg_XF>0$ and $\deg_YF>0$, then $F\mid P$.
--
--   In the source this is proved by contradiction on the normalization $\mathcal X_F$ of the curve $F=0$:
--
--   1. Bézout's theorem together with the row and column divisibilities gives the lower bound $\Gamma_F\ge(h-2t)(a+b)$ on the weighted number of subgroup-grid points on the curve.
--   2. The Corvaja–Zannier estimate (Theorem 4.12) gives the upper bound $\Gamma_F\le C(N^{1/3}(ab)^{2/3}+ab)$.
--   3. The multiplicatively dependent (binomial) case is handled directly.
--
--   Over $K$, cancelling mixed factors and interpolating the pure part then give $E\mid P$, and the divisibility descends to $\mathbb F_q$.
--
--   **Formalization Note** $K$ is `AlgebraicClosure (ZMod q)`, and the elements of $S_i$ are mapped into $K$ by `algebraMap`. $P(\alpha,Y)$ is the univariate polynomial obtained by substituting $\alpha$ for $X=X_0$.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), proof of Lemma 4.13, pp.24-25 (PDF pp.26-27): 'We work first over K ... We have shown that every mixed irreducible factor of E divides P'

import Mathlib

namespace PrivPCP

theorem lemma_4_13_mixed_closure : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
      Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
      ∀ k₁ k₂ : ℕ, k₁ < Nat.card S₁ → k₂ < Nat.card S₂ →
      ∀ E P : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q)), E ≠ 0 →
        (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤
          c₀ * ((min (Nat.card S₁ - k₁) (Nat.card S₂ - k₂) : ℕ) : ℝ) ^ 3 / ((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) →
        P.degreeOf 0 < k₁ + E.degreeOf 0 →
        P.degreeOf 1 < k₂ + E.degreeOf 1 →
        (∀ α ∈ S₁, ∃ R : Polynomial (AlgebraicClosure (ZMod q)),
          MvPolynomial.aeval (![Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (α : ZMod q)),
            Polynomial.X] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) P =
          MvPolynomial.aeval (![Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (α : ZMod q)),
            Polynomial.X] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) E * R) →
        (∀ β ∈ S₂, ∃ Cβ : Polynomial (AlgebraicClosure (ZMod q)),
          MvPolynomial.aeval (![Polynomial.X, Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
            (β : ZMod q))] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) P =
          MvPolynomial.aeval (![Polynomial.X, Polynomial.C (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
            (β : ZMod q))] : Fin 2 → Polynomial (AlgebraicClosure (ZMod q))) E * Cβ) →
        ∀ F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q)), Irreducible F → F ∣ E →
          0 < F.degreeOf 0 → 0 < F.degreeOf 1 → F ∣ P := by sorry

end PrivPCP
