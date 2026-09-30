-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_normalized_jet_contact_certificate
-- name    : WeierstrassEllipticZeta.normalized_jet_contact_certificate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T21:59:05.232086+00:00
-- url     : https://prove2.me/theorems/cd8b8b3c-cacc-4551-abad-841f71e30066
-- title:
--   Low normalized jets are nonzero contact polynomials
-- statement:
--   Let G be the mission's compact elliptic-extension geometry, let m,n,U be natural numbers, let X be a finite set of complex numbers containing 0, and suppose Q has the chart certificates in `Frontier.HasChartCertificates G m n U X Q`.
--
--   For a chart c and 0≤k≤2U, set
--
--   $$p_{c,k}=D_c^k(\operatorname{Normalize}_c Q).$$
--
--   Then p_ck belongs to the order-(U+1) contact ideal at every point of X where chart c is valid. If at least one such point exists, p_ck is a nonzero polynomial. No extra local-order or derivative-degree assumptions are required for this certificate; the finite orders already contained in the chart certificates suffice.
-- source:
--   Derived normalized-jet contact certificate for the frontier https://prove2.me/theorems/b9f04d31-9d16-4432-b4ad-69b15ccf7af4. The mission context is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The complete proof derives a finite family from the existing ChartCertificate.polynomial.triangular.orders and Geometry.hcontact hypotheses, using Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, Logic/Function/Iterate.lean (iterate_add_apply, iterate_succ_apply'). The remaining child is a sufficient finite-family weight criterion, not an asserted equivalent reformulation of unrestricted contact-polynomial choice. Its uniform geometric estimate and the main mission theorem remain open.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry

open WeierstrassEllipticZeta
open scoped Pointwise Classical

theorem WeierstrassEllipticZeta.normalized_jet_contact_certificate
    (G : Frontier.Geometry) (m n U : ℕ) (X : Finset ℂ) (hX : 0 ∈ X)
    (Q : MvPolynomial (Fin 7) ℂ)
    (hcharts : Frontier.HasChartCertificates G m n U X Q)
    (c : Fin 2) (k : ℕ) (hk : k ≤ 2 * U) :
    (∀ z ∈ X, G.S (extensionChartDenominator c) z ≠ 0 →
      (extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q) ∈
        extensionChartContactIdeal G.L.g₂ G.L.g₃ c
          (extensionChartCoordinates G.S c z) (U + 1)) ∧
    ((∃ z ∈ X, G.S (extensionChartDenominator c) z ≠ 0) →
      (extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k]
        (extensionChartNormalize c Q) ≠ 0) := by sorry
