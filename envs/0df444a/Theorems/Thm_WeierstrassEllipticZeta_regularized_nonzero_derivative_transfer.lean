-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_regularized_nonzero_derivative_transfer
-- name    : WeierstrassEllipticZeta.regularized_nonzero_derivative_transfer
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T02:10:54.141148+00:00
-- url     : https://prove2.me/theorems/3ca1be8c-3a7b-411d-a9f8-e6f85f2b885d
-- title:
--   Transfer of a nonzero derivative through elliptic regularization
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and Weierstrass function $\wp$. Fix $v\in\mathbb C$ and integers $e,M\ge0$ with $e\ge6M$. Let $F,\sigma,S,G:\mathbb C\to\mathbb C$ satisfy:
--
--   - $F$ is analytic at every $z$ such that $z+v\notin\Lambda$;
--   - $\sigma,S,G$ are entire;
--   - $S(z)=\sigma(z)^2\wp(z)$ whenever $z\notin\Lambda$;
--   - whenever $z,z+v\notin\Lambda$,
--     $$G(z)=\sigma(z)^e[2(\wp(v)-\wp(z))]^{3M}F(z).$$
--
--   Then, for every $z$ with $z+v\notin\Lambda$ and every integer $t\ge0$ for which $G^{(t)}(z)\ne0$, there is an integer $0\le n\le t$ such that $F^{(n)}(z)\ne0$.
--
--   In particular $z$ may belong to the lattice. There is no nonvanishing or normalization hypothesis on $\sigma$, and $v$ need not be regular; the displayed identities use the given total functions. The conclusion follows from the entire multiplier
--
--   $$H(z)=\sigma(z)^{e-6M}[2(\wp(v)\sigma(z)^2-S(z))]^{3M}.$$
--
--   It extends the off-lattice factorization $G=HF$ across lattice points wherever $F$ is analytic, and multiplication by an analytic function cannot decrease vanishing order.
-- source:
--   Analytic factorization step in Senthil Kumar K (2026), proof of Lemma 9, https://doi.org/10.1017/S001309152610145X. This derived formulation uses any exponent e>=6M and an entire extension of sigma^2*wp to prove transfer with no loss of derivative order, including at lattice points. The explicit factorization is a generalized implementation of the vanishing-order argument, not a quoted statement from the source.

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open WeierstrassEllipticZeta Set

theorem WeierstrassEllipticZeta.regularized_nonzero_derivative_transfer
    (L : PeriodPair) (v : ℂ) (F σ S G : ℂ → ℂ) (e M : ℕ)
    (he : 6 * M ≤ e)
    (hF : AnalyticOnNhd ℂ F {z : ℂ | z + v ∉ L.lattice})
    (hσ : AnalyticOnNhd ℂ σ univ)
    (hS : AnalyticOnNhd ℂ S univ)
    (hG : AnalyticOnNhd ℂ G univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → S z = σ z ^ 2 * L.weierstrassP z)
    (hG_value : ∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
      G z = σ z ^ e * (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) * F z) :
    ∀ z : ℂ, z + v ∉ L.lattice → ∀ t : ℕ, iteratedDeriv t G z ≠ 0 →
      ∃ n ≤ t, iteratedDeriv n F z ≠ 0 := by sorry
