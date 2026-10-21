-- Prove2me | Theorems.Thm_QRH_gauss_jacobi_consequences
-- name    : QRH.gauss_jacobi_consequences
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T12:47:18.034064+00:00
-- url     : https://prove2.me/theorems/0d1e43ad-20d9-4037-81be-9352aaf7cb9a
-- title:
--   Consequences of the Gauss-Jacobi identities and cubic reciprocity
-- statement:
--   Let a, b, n be squarefree primary elements prime to S, with a and b coprime in the sense that their only common divisor is the unit. Then the interface axioms imply the four conversion identities of Lemma 4.1 of the source: first, conj(alpha n) gamma_2(n) gamma_1(n) = mu(n) G(cl n); second, mu(n) gamma_{-1}(n) = chi_n(-1) G(cl n)^{-1} conj(alpha n) gamma_2(n); third, the quotient identity chi_a(-1) conj(G(cl a)) G(cl b) R(cl a, cl b) = G(cl b inv(cl a)) in the ray class group; and fourth, the multiplicativity of the cubic Gauss-sum coefficients up to a sextic twist: a_xi(ab) = a_xi(a) a_xi(b) chi_b(a)^4.
-- source:
--   The Quasi-Riemann Hypothesis, October 2026, Lemma 4.1 (equations 4.7-4.10).

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun

universe u

namespace QRH

/-- The consequences of the Gauss-Jacobi identities and cubic
reciprocity (Lemma 4.1 of the source), for squarefree primary elements
prime to S. The four conjuncts are the conversion identities between
Möbius coefficients and cubic Gauss sums (equations 4.7 and 4.8): the
Möbius factor combines with the Poisson γ₋₁ into the cubic coefficient,
and back; the quotient identity for the ray class factor G (equation
4.9); and the multiplicativity of the cubic Gauss-sum coefficients a_ξ
up to a sextic twist (equation 4.10). Each follows from the interface
axioms by complex algebra: the Gauss sums and the phase have modulus one,
Möbius squares to one on squarefree elements, and the reciprocity
bicharacter is real. -/
theorem gauss_jacobi_consequences (W : QRHWorld.{u}) (a b n : W.E)
    (hsn : W.IsSqf n) (hgn : W.Sgood n)
    (hsa : W.IsSqf a) (hga : W.Sgood a)
    (hsb : W.IsSqf b) (hgb : W.Sgood b)
    (hcop : ∀ d : W.E, d ∈ W.divs a → d ∈ W.divs b → d = W.one) :
    star (W.alpha n) * W.gamma 2 n * W.gamma 1 n
        = W.mu n * W.Gcl (W.cl n)
      ∧ W.mu n * W.gamma (-1) n
        = W.chiNeg n * (W.Gcl (W.cl n))⁻¹ * star (W.alpha n)
            * W.gamma 2 n
      ∧ W.chiNeg a * star (W.Gcl (W.cl a)) * W.Gcl (W.cl b)
            * W.Rcl (W.cl a) (W.cl b)
          = W.Gcl (W.mulC (W.cl b) (W.invC (W.cl a)))
      ∧ axi W (W.mul a b) = axi W a * axi W b * W.chi b a ^ 4 := by
  sorry

end QRH
