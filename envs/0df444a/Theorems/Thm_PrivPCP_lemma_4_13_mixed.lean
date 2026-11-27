-- Prove2me | Theorems.Thm_PrivPCP_lemma_4_13_mixed
-- name    : PrivPCP.lemma_4_13_mixed
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T02:49:04.457827+00:00
-- url     : https://prove2.me/theorems/fb784430-9e32-5f77-9103-9c56af9cf9cb
-- title:
--   Lemma 4.13, main step: mixed irreducible factors of $E$ divide $P$
-- statement:
--   This is the main step in the proof of Lemma 4.13 of the source: under the hypotheses of that lemma, every irreducible factor of $E$ that involves both variables divides $P$.
--
--   There is an absolute constant $c_0>0$ such that the following holds. Let $q$ be prime, let $S_1,S_2\le\mathbb F_q^\times$ be subgroups of coprime orders $n_1,n_2$, and fix integers $0\le k_i<n_i$. Put $N=n_1n_2$ and $h=\min\{n_1-k_1,n_2-k_2\}$. Let $E,P\in\mathbb F_q[X,Y]$ with $E\ne0$, $e_X=\deg_XE$, $e_Y=\deg_YE$ and $t=\max\{e_X,e_Y\}$. Suppose
--
--   $$t\le c_0\frac{h^3}{N},\qquad \deg_XP<k_1+e_X,\qquad \deg_YP<k_2+e_Y,$$
--
--   and that for every $\alpha\in S_1$ and $\beta\in S_2$ there are polynomials $R_\alpha(Y)$, $C_\beta(X)$ with
--
--   $$P(\alpha,Y)=E(\alpha,Y)R_\alpha(Y),\qquad P(X,\beta)=E(X,\beta)C_\beta(X).$$
--
--   If $F\in\mathbb F_q[X,Y]$ is irreducible, $F\mid E$, $\deg_XF>0$ and $\deg_YF>0$, then $F\mid P$.
--
--   In the source this is the statement "every mixed irreducible factor of $E$ divides $P$", proved by contradiction: the subgroup structure gives a lower bound on the weighted number $\Gamma_F$ of grid points on the curve $F=0$, and the Corvaja–Zannier gcd estimate (Theorem 4.12) gives an upper bound. The remaining steps of Lemma 4.13 are elementary: cancelling mixed factors one at a time, and handling the leftover factor $U(X)V(Y)$ by interpolation.
--
--   **Formalization Note** $\mathbb F_q[X,Y]$ is `MvPolynomial (Fin 2) (ZMod q)` with $X=X_0$, $Y=X_1$. $P(\alpha,Y)$ is the univariate polynomial obtained by substituting $\alpha$ for $X$. Irreducibility is over $\mathbb F_q$. The source argues over $\overline{\mathbb F}_q$; an $\mathbb F_q$-irreducible mixed factor is a product of distinct Galois-conjugate mixed $\overline{\mathbb F}_q$-irreducible factors, each of which divides $P$ by the source's argument.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), proof of Lemma 4.13, pp.24-25 (PDF pp.26-27): 'We have shown that every mixed irreducible factor of E divides P' (using Theorem 4.12)

import Mathlib

namespace PrivPCP

theorem lemma_4_13_mixed : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
      Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
      ∀ k₁ k₂ : ℕ, k₁ < Nat.card S₁ → k₂ < Nat.card S₂ →
      ∀ E P : MvPolynomial (Fin 2) (ZMod q), E ≠ 0 →
        (max (E.degreeOf 0) (E.degreeOf 1) : ℝ) ≤
          c₀ * ((min (Nat.card S₁ - k₁) (Nat.card S₂ - k₂) : ℕ) : ℝ) ^ 3 / ((Nat.card S₁ * Nat.card S₂ : ℕ) : ℝ) →
        P.degreeOf 0 < k₁ + E.degreeOf 0 →
        P.degreeOf 1 < k₂ + E.degreeOf 1 →
        (∀ α ∈ S₁, ∃ R : Polynomial (ZMod q),
          MvPolynomial.aeval (![Polynomial.C (α : ZMod q), Polynomial.X] : Fin 2 → Polynomial (ZMod q)) P =
            MvPolynomial.aeval (![Polynomial.C (α : ZMod q), Polynomial.X] : Fin 2 → Polynomial (ZMod q)) E * R) →
        (∀ β ∈ S₂, ∃ Cβ : Polynomial (ZMod q),
          MvPolynomial.aeval (![Polynomial.X, Polynomial.C (β : ZMod q)] : Fin 2 → Polynomial (ZMod q)) P =
            MvPolynomial.aeval (![Polynomial.X, Polynomial.C (β : ZMod q)] : Fin 2 → Polynomial (ZMod q)) E * Cβ) →
        ∀ F : MvPolynomial (Fin 2) (ZMod q), Irreducible F → F ∣ E →
          0 < F.degreeOf 0 → 0 < F.degreeOf 1 → F ∣ P := by sorry

end PrivPCP
