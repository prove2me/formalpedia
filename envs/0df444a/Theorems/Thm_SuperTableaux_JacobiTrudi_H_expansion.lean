-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_H_expansion
-- name    : SuperTableaux.JacobiTrudi.H_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:50.670322+00:00
-- url     : https://prove2.me/theorems/ed6895f0-b8a9-4499-8edc-46e68571e586
-- title:
--   Proof of Theorem 4.5, p. 23 — $H^{\mathcal A/\mathcal B}_\mu=\sum_{\langle\lambda\rangle=\langle\mu\rangle}K_{\lambda\mu}S^{\mathcal A/\mathcal B}_\lambda$
-- statement:
--   Let $\mathcal A,\mathcal B$ be **infinite**, linearly ordered, at most countable, $\mathbb Z_2$-graded sets, $n\ge1$ and $\mu\in\mathbb Z^n_+$. Put $H^{\mathcal A/\mathcal B}_\mu=\prod_{i=1}^n S^{\mathcal A/\mathcal B}_{\mu_i}$. Then
--   $$H^{\mathcal A/\mathcal B}_\mu=\sum_{\substack{\lambda\in\mathbb Z^n_+\\ \langle\lambda\rangle=\langle\mu\rangle}}K_{\lambda\mu}\,S^{\mathcal A/\mathcal B}_\lambda ,$$
--   where $\langle\lambda\rangle=\sum_i\lambda_i$ and $K_{\lambda\mu}$ is the number of rational $[n]$-semistandard tableaux of shape $\lambda$ with content $\mu$. The sum is in general infinite and converges coefficientwise.
--
--   This is the first step of the proof of the Jacobi–Trudi formula: with the triangularity of $K$ it lets one invert the system and compare with the classical identities (4.5).
--
--   **Formalization Note** The infinite sum is a `HasSum` in the coefficientwise (product) topology on `MvPowerSeries (A ⊕ B) ℤ`, with $\mathbb Z$ discrete, so convergence means that each coefficient receives finitely many nonzero contributions. `tsum` is not used, since its junk value $0$ for non-summable families would hide divergence. The ring $\mathbb Z[[x_{\mathcal A},x_{\mathcal B}^{-1}]]$ is `MvPowerSeries (A ⊕ B) ℤ`: the variable `Sum.inl a` is $x_a$ and the variable `Sum.inr b` is the symbol $x_b^{-1}$, so a monomial with exponent vector $m$ is $\prod_a x_a^{m(a)}\prod_b (x_b^{-1})^{m(b)}$; this is literally a power-series ring in the symbols $x_a$ and $x_b^{-1}$. A/B-tableaux are encoded in cut coordinates (see the definitions item).
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, p. 23, proof of Theorem 4.5

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting
open scoped MvPowerSeries.WithPiTopology

namespace SuperTableaux.JacobiTrudi
theorem H_expansion {A B : Type*} [LinearOrder A] [Countable A] [Infinite A]
    [LinearOrder B] [Countable B] [Infinite B] (oddA : A → Bool) (oddB : B → Bool)
    (n : ℕ) (hn : 0 < n) (mu : GenPartition n) :
    HasSum (fun la : {la : GenPartition n // ∑ i, la.1 i = ∑ i, mu.1 i} =>
        (kostka la.1 mu : ℤ) • charAB oddA oddB la.1) (Hprod oddA oddB mu) := by sorry
end SuperTableaux.JacobiTrudi
