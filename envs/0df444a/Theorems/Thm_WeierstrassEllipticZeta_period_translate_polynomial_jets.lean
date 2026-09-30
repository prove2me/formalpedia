-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_period_translate_polynomial_jets
-- name    : WeierstrassEllipticZeta.period_translate_polynomial_jets
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T14:33:25.049437+00:00
-- url     : https://prove2.me/theorems/e1c185fd-6d90-4aa3-a7b6-18ba6bef4f8d
-- title:
--   Polynomial derivative formulas and coefficient bounds at period translates
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$ and canonical functions $\zeta,\wp,\wp'$. Let $\omega\in\mathbb C$ and write $\eta=\eta_L(\omega)$ for its canonical quasi-period. Assume
--
--   $$\zeta'(z)=-\wp(z)\qquad(z\notin\Omega),$$
--
--   $$\wp(z+a\omega)=\wp(z),\qquad \zeta(z+a\omega)=\zeta(z)+a\eta
--   \qquad(z\notin\Omega,\ a\in\mathbb Z).$$
--
--   In the polynomial ring $\mathbb Z[X_0,\ldots,X_6]$, define the derivation $\mathcal D$ by
--
--   $$(\mathcal D X_0,\ldots,\mathcal D X_6)=(1,0,0,-X_4,X_5,X_6,12X_4X_5).$$
--
--   For any integer $a$ and nonnegative integers $\ell_0,\ell_2,\ell_3,n$, put
--
--   $$P_a=(X_0+aX_1)^{\ell_0}X_4^{\ell_2}(X_3+aX_2)^{\ell_3},
--   \qquad K=\ell_0+\ell_2+\ell_3+n.$$
--
--   Let $\mathscr L(P)$ denote the sum of the absolute values of all integer coefficients. Then
--
--   $$\deg(\mathcal D^nP_a)\le K,\qquad
--   \mathscr L(\mathcal D^nP_a)\le n!\,24^K(1+|a|)^{\ell_0+\ell_3}.$$
--
--   At every $z\notin\Omega$, evaluation at the seven basic values gives the actual translated derivative:
--
--   $$\left.\frac{d^n}{dw^n}\big(w^{\ell_0}\wp(w)^{\ell_2}\zeta(w)^{\ell_3}\big)
--   \right|_{w=z+a\omega}
--   =(\mathcal D^nP_a)(z,\omega,\eta,\zeta(z),\wp(z),\wp'(z),\wp''(z)).$$
--
--   This gives a universal integer polynomial for every derivative at a period translate. It includes negative and zero $a$, all zero exponents, and derivative order zero. It is a supporting formulation of the calculation following equation (28), with an explicit coarse coefficient bound rather than the source's displayed numerical estimate.
-- source:
--   Supporting formulation of Senthil Kumar K (2026), Section 5, the remark following Lemma 7, equation (28) and the subsequent derivative expansion and coefficient estimate, using the differential identities in Section 4, equations (8)-(9). The polynomial derivation and the explicit bound n! 24^K (1+|a|)^(l0+l3) formalize that calculation; the numerical bound is not claimed to be verbatim. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_PeriodJets

open MvPolynomial WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.period_translate_polynomial_jets (L : PeriodPair) (ω : ℂ)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hperiod : ∀ (z : ℂ) (a : ℤ), z ∉ L.lattice →
      L.weierstrassP (z + a * ω) = L.weierstrassP z ∧
      weierstrassZeta L (z + a * ω) = weierstrassZeta L z + a * zetaQuasiPeriod L ω)
    (a : ℤ) (l₀ l₂ l₃ n : ℕ) :
    (periodJetDerivation^[n] (periodJetPolynomial a l₀ l₂ l₃)).totalDegree ≤
      l₀ + l₂ + l₃ + n ∧
    (∑ m ∈ (periodJetDerivation^[n] (periodJetPolynomial a l₀ l₂ l₃)).support,
      ((periodJetDerivation^[n] (periodJetPolynomial a l₀ l₂ l₃)).coeff m).natAbs) ≤
        n.factorial * 24 ^ (l₀ + l₂ + l₃ + n) * (1 + a.natAbs) ^ (l₀ + l₃) ∧
    ∀ z : ℂ, z ∉ L.lattice →
      iteratedDeriv n (fun w => w ^ l₀ * L.weierstrassP w ^ l₂ *
        weierstrassZeta L w ^ l₃) (z + a * ω) =
          eval₂ (Int.castRingHom ℂ) (periodJetCoordinates L ω z)
            (periodJetDerivation^[n] (periodJetPolynomial a l₀ l₂ l₃)) := by sorry
