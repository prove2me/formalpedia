-- Prove2me | Theorems.Thm_PrivPCP_lemma_4_13
-- name    : PrivPCP.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:42:35.025084+00:00
-- url     : https://prove2.me/theorems/98c7810f-6662-44ed-9070-12989a299a88
-- title:
--   Lemma 4.13: bivariate divisibility on a coprime subgroup grid
-- statement:
--   There is an absolute constant $c_0>0$ such that the following holds. Let $q$ be prime, let $S_1,S_2\le\mathbb F_q^\times$ be subgroups of coprime orders $n_1,n_2$, and fix integers $0\le k_i<n_i$. Put $N=n_1n_2$ and $h=\min\{n_1-k_1,n_2-k_2\}$. Let $E,P\in\mathbb F_q[X,Y]$ with $E\ne0$, $e_X=\deg_XE$, $e_Y=\deg_YE$ and $t=\max\{e_X,e_Y\}$. Suppose
--   $$t\le c_0\frac{h^3}{N},\qquad \deg_XP<k_1+e_X,\qquad \deg_YP<k_2+e_Y,$$
--   and that for every $\alpha\in S_1$ and $\beta\in S_2$ there are polynomials $R_\alpha(Y)$, $C_\beta(X)$ with
--   $$P(\alpha,Y)=E(\alpha,Y)R_\alpha(Y),\qquad P(X,\beta)=E(X,\beta)C_\beta(X).$$
--   Then $E\mid P$, and $P=EQ$ for some $Q$ with $\deg_XQ<k_1$ and $\deg_YQ<k_2$.
--
--   This replaces the condition $t+k<n/2$ of Polishchuk–Spielman's divisibility lemma, which forces rates below $1/2$; it is the algebraic core of Theorem 4.11.
--
--   **Formalization Note** $\mathbb F_q[X,Y]$ is the polynomial ring in two variables $X=X_0$, $Y=X_1$; $P(\alpha,Y)$ is the univariate polynomial obtained by substituting $\alpha$ for $X$.
--
--   Differences from the source:
--   - encoding: $P(\alpha,Y)$, $P(X,\beta)$ → substitution of $\alpha$ for $X_0$ (resp. $\beta$ for $X_1$) into a polynomial in `Fin 2` variables; reason: same polynomials
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Lemma 4.13, p.24 (PDF p.26)

import Mathlib

namespace PrivPCP

/-- **Lemma 4.13 (Coprime-subgroup bivariate divisibility)** (Bafna, Vyas, *Private PCPs from Product
Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Lemma 4.13, p.24). There is an absolute
constant `c₀ > 0` such that: for every prime `q`, subgroups `S_1, S_2 ⩽ 𝔽_q^×` of coprime orders `n_1, n_2`,
integers `0 ⩽ k_i < n_i`, `N = n_1 n_2`, `h = min{n_1 − k_1, n_2 − k_2}`, and `E, P ∈ 𝔽_q[X, Y]` with `E ≠ 0`,
`e_X = deg_X E`, `e_Y = deg_Y E`, `t = max{e_X, e_Y}`: if `t ⩽ c₀ h³/N`, `deg_X P < k_1 + e_X`,
`deg_Y P < k_2 + e_Y`, and for every `α ∈ S_1`, `β ∈ S_2` there are `R_α(Y)`, `C_β(X)` with
`P(α, Y) = E(α, Y) R_α(Y)` and `P(X, β) = E(X, β) C_β(X)`, then `E ∣ P`, and `P = EQ` for some `Q` with
`deg_X Q < k_1`, `deg_Y Q < k_2`.

**Formalization Note** `𝔽_q[X, Y]` is `MvPolynomial (Fin 2) (ZMod q)` with `X = X 0`, `Y = X 1`. `P(α, Y)` is
the univariate polynomial obtained by substituting `α` for `X` (`aeval ![C α, X]`), and `P(X, β)` likewise. -/
theorem lemma_4_13 : ∃ c₀ : ℝ, 0 < c₀ ∧
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
        E ∣ P ∧ ∃ Q : MvPolynomial (Fin 2) (ZMod q), P = E * Q ∧ Q.degreeOf 0 < k₁ ∧ Q.degreeOf 1 < k₂ := by sorry

end PrivPCP
