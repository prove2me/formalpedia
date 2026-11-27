-- Prove2me | Theorems.Thm_PrivPCP_lemma_4_13_kpos
-- name    : PrivPCP.lemma_4_13_kpos
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T02:29:51.351607+00:00
-- url     : https://prove2.me/theorems/9eace8fa-b70d-582c-9b37-b0f2f2a00f5a
-- title:
--   Lemma 4.13 (for $k_1,k_2\ge1$): bivariate divisibility on a coprime subgroup grid
-- statement:
--   This is Lemma 4.13 of the source in the case $k_1,k_2\ge1$, which is the case Theorem 4.11 uses.
--
--   There is an absolute constant $c_0>0$ such that the following holds. Let $q$ be prime, let $S_1,S_2\le\mathbb F_q^\times$ be subgroups of coprime orders $n_1,n_2$, and fix integers $1\le k_i<n_i$. Put $N=n_1n_2$ and $h=\min\{n_1-k_1,n_2-k_2\}$. Let $E,P\in\mathbb F_q[X,Y]$ with $E\ne0$, $e_X=\deg_XE$, $e_Y=\deg_YE$ and $t=\max\{e_X,e_Y\}$. Suppose
--
--   $$t\le c_0\frac{h^3}{N},\qquad \deg_XP<k_1+e_X,\qquad \deg_YP<k_2+e_Y,$$
--
--   and that for every $\alpha\in S_1$ and $\beta\in S_2$ there are polynomials $R_\alpha(Y)$, $C_\beta(X)$ with
--
--   $$P(\alpha,Y)=E(\alpha,Y)R_\alpha(Y),\qquad P(X,\beta)=E(X,\beta)C_\beta(X).$$
--
--   Then $E\mid P$, and $P=EQ$ for some $Q$ with $\deg_XQ<k_1$ and $\deg_YQ<k_2$.
--
--   This is the divisibility lemma that replaces the condition $t+k<n/2$ of Polishchuk–Spielman's lemma, which forces rates below $1/2$. Together with the Polishchuk–Spielman argument it gives the two-dimensional product expansion of subgroup Reed–Solomon codes (Theorem 4.11).
--
--   **Formalization Note** $\mathbb F_q[X,Y]$ is the polynomial ring in the variables $X=X_0$, $Y=X_1$, and $P(\alpha,Y)$ is the univariate polynomial obtained by substituting $\alpha$ for $X$. The source allows $0\le k_i$. With Lean's convention $\deg 0=0$ (rather than $-\infty$) the case $k_i=0$ is false: $E=XY$, $P=0$, $k_1=k_2=0$ is a counterexample, recorded by the disproof of `PrivPCP.lemma_4_13`. Requiring $k_i\ge1$ removes exactly this degenerate case; Theorem 4.11 only uses $k_i\ge1$.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Lemma 4.13, p.24 (PDF p.26), restricted to k_i >= 1 (the case used in the proof of Theorem 4.11, pp.25-26)

import Mathlib

namespace PrivPCP

theorem lemma_4_13_kpos : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (q : ℕ) [Fact q.Prime] (S₁ S₂ : Subgroup (ZMod q)ˣ),
      Nat.Coprime (Nat.card S₁) (Nat.card S₂) →
      ∀ k₁ k₂ : ℕ, 1 ≤ k₁ → 1 ≤ k₂ → k₁ < Nat.card S₁ → k₂ < Nat.card S₂ →
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
        E ∣ P ∧ ∃ Q : MvPolynomial (Fin 2) (ZMod q), P = E * Q ∧ Q.degreeOf 0 < k₁ ∧ Q.degreeOf 1 < k₂ := by sorry

end PrivPCP
