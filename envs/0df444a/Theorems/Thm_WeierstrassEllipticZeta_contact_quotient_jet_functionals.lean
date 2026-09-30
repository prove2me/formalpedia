-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_contact_quotient_jet_functionals
-- name    : WeierstrassEllipticZeta.contact_quotient_jet_functionals
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T17:10:52.871722+00:00
-- url     : https://prove2.me/theorems/fe9b5b39-fbcf-4242-b9fa-bee42860cdac
-- title:
--   Finite jet representation of contact-quotient linear maps
-- statement:
--   Fix the stable elliptic geometry G, a chart c, a finite set Z of complex points, a natural contact order N, and any complex vector space L. Let I be the intersection over Z of the order-N chart contact ideals. Every complex-linear map from the polynomial quotient A/I to L can be expressed, on every polynomial p, as a finite sum of its chart jets of orders 0 through N−1 at points of Z, with weights in L.
--
--   Conversely, each choice of those weights defines a unique complex-linear map on the quotient. The weights representing a given map are not asserted to be unique. Empty Z and N=0 are included. The jets here are evaluations of iterated chart derivations; no assertion about analytic evaluation at a singular chart point is made. No extra finite-dimensionality or reducedness hypothesis on the quotient is needed.
-- source:
--   Derived finite-jet representation step for https://prove2.me/theorems/2fc7a002-4ac8-40ce-af14-a8aebb8fae9f. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is a derived linear-algebra tool for the formal development, not a completion of the zero estimate. Primary Lean sources: Mathlib LinearAlgebra/Basis/VectorSpace.lean, LinearAlgebra/Isomorphisms.lean and LinearAlgebra/Pi.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. The stable geometry contact-ideal membership axiom identifies the kernel of the finite jet map. Embedding the contact quotient into the jet-coordinate space and extending a linear map gives a finite weighted-jet representation; every weight array defines a unique quotient map.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Pi

noncomputable section
open scoped Classical
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.contact_quotient_jet_functionals
    (G : Frontier.Geometry) (c : Fin 2) (Z : Finset ℂ) (N : ℕ)
    (L : Type*) [AddCommGroup L] [Module ℂ L] :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ c
        (extensionChartCoordinates G.S c z.val) N
    (∀ T : (MvPolynomial (Fin 4) ℂ ⧸ I) →ₗ[ℂ] L,
      ∃ w : Z × Fin N → L, ∀ p : MvPolynomial (Fin 4) ℂ,
        T (Ideal.Quotient.mk I p) = ∑ r : Z × Fin N,
          MvPolynomial.eval (extensionChartCoordinates G.S c r.1.val)
            ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[r.2.val] p) • w r) ∧
    (∀ w : Z × Fin N → L,
      ∃! T : (MvPolynomial (Fin 4) ℂ ⧸ I) →ₗ[ℂ] L,
        ∀ p : MvPolynomial (Fin 4) ℂ,
          T (Ideal.Quotient.mk I p) = ∑ r : Z × Fin N,
            MvPolynomial.eval (extensionChartCoordinates G.S c r.1.val)
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[r.2.val] p) • w r) := by sorry
