-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_regularization_preserves_nonvanishing
-- name    : WeierstrassEllipticZeta.regularization_preserves_nonvanishing
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T11:56:19.953241+00:00
-- url     : https://prove2.me/theorems/b87af541-0501-4acb-aeb6-80d3e05a9799
-- title:
--   Elliptic regularization preserves nonvanishing
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and Weierstrass function $\wp$. Fix $v\in\mathbb C$, integers $e,M\ge0$, and functions $F,\sigma,G:\mathbb C\to\mathbb C$. Assume:
--
--   - $F$ is continuous at every $z$ with $z+v\notin\Lambda$;
--   - $\sigma(z)\ne0$ for every $z\notin\Lambda$;
--   - for every $z$ with $z,z+v\notin\Lambda$,
--     $$G(z)=\sigma(z)^e[2(\wp(v)-\wp(z))]^{3M}F(z);$$
--   - there is a point $z_0$ with $z_0+v\notin\Lambda$ and $F(z_0)\ne0$.
--
--   Then $G$ is not the zero function.
--
--   No analyticity or continuity assumption on $G$ or $\sigma$ is required, no bound on the exponents is imposed, and $z_0$ may be a lattice point. The value $\wp(v)$ is the given total function value; regularity of $v$ is not assumed. The conclusion follows from lattice discreteness, continuity of $F$, and the impossibility of a constant germ of $\wp$ at a regular point.
-- source:
--   Senthil Kumar K (2026), proof of Lemma 9, the implication from nonzero F to nonzero sigma-regularized G, https://doi.org/10.1017/S001309152610145X. This generalized continuity formulation supplies the implication explicitly using lattice discreteness, the identity principle and the double pole of wp. It is a derived supporting lemma, not a quoted source statement.

import Definitions.Def_WeierstrassEllipticZeta_Defs

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.regularization_preserves_nonvanishing
    (L : PeriodPair) (v : ℂ) (F σ G : ℂ → ℂ) (e M : ℕ)
    (hF : ∀ z : ℂ, z + v ∉ L.lattice → ContinuousAt F z)
    (hσ : ∀ z : ℂ, z ∉ L.lattice → σ z ≠ 0)
    (hG : ∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
      G z = σ z ^ e * (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) * F z)
    (h_nonzero : ∃ z : ℂ, z + v ∉ L.lattice ∧ F z ≠ 0) :
    G ≠ 0 := by sorry
