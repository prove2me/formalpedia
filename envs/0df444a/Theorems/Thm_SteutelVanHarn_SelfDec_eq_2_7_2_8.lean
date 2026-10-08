-- Prove2me | Theorems.Thm_SteutelVanHarn_SelfDec_eq_2_7_2_8
-- name    : SteutelVanHarn.SelfDec.eq_2_7_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:51:00.814212+00:00
-- url     : https://prove2.me/theorems/f952be56-3062-4060-a46e-cda1e56bffde
-- title:
--   (2.7)–(2.8) — the form (2.4) gives $P'/P=\lambda(1-G)/(1-z)$ and the nonincreasing $r_n=\lambda\sum_{j>n}g_j$
-- statement:
--   Let $(p_n)$ be a distribution on $\mathbb N_0$ with p.g.f. $P$ and $0<p_0<1$, and suppose $P$ has the canonical form
--   $$
--   P(z)=\exp\Big\{-\lambda\int_z^1\frac{1-G(u)}{1-u}\,du\Big\}\qquad(0\le z<1)\tag{2.4}
--   $$
--   with $\lambda>0$ and $G$ the p.g.f. of a distribution $(g_n)$ on $\mathbb N_0$ with $g_0=0$. Then
--
--   1. $R(z):=P'(z)/P(z)=\lambda\,\dfrac{1-G(z)}{1-z}$ for $0\le z<1$ (2.7);
--   2. $(p_n)$ is infinitely divisible;
--   3. its canonical sequence is
--   $$
--   r_n=\lambda\Big(1-\sum_{j=1}^{n}g_j\Big)=\lambda\sum_{j=n+1}^{\infty}g_j\qquad(n\in\mathbb N_0);\tag{2.8}
--   $$
--   4. $(r_n)$ is nonincreasing.
--
--   This is the step of the proof of Theorem 2.2 that compares (2.4) with the form (1.4) of Lemma 1.2.
--
--   **Formalization Note** $P'$ is Lean's `deriv` of `pgf p`; the form (2.4) includes the finiteness of the integral for each $z\in[0,1)$.
-- source:
--   Steutel & van Harn, Discrete analogues of self-decomposability and stability, Memorandum COSOR 78-07, TH Eindhoven (1978), p. 3, proof of Theorem 2.2, (2.7), (2.8)

import Definitions.Def_SteutelVanHarn_SelfDec_SelfDec

namespace SteutelVanHarn.SelfDec

theorem eq_2_7_2_8 (p : ℕ → ℝ) (hp : IsDistribution p) (hp0 : 0 < p 0) (hp1 : p 0 < 1)
    (lam : ℝ) (g : ℕ → ℝ) (h24 : HasForm24 p lam g) :
    (∀ z ∈ Set.Ico (0 : ℝ) 1, deriv (pgf p) z / pgf p z = lam * ((1 - pgf g z) / (1 - z))) ∧
    IsInfDiv p ∧
    (∀ n : ℕ, canonicalSeq p n = lam * (1 - ∑ j ∈ Finset.Icc 1 n, g j)) ∧
    (∀ n : ℕ, canonicalSeq p n = lam * ∑' j : ℕ, g (n + 1 + j)) ∧
    Antitone (canonicalSeq p) := by sorry

end SteutelVanHarn.SelfDec
