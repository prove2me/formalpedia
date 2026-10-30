-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P26_renyi_qInverseDerivative
-- name    : QAlgorithms.Papers.Independent.Advance50.P26.renyi_qInverseDerivative
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T10:42:29.289704+00:00
-- url     : https://prove2.me/theorems/264ca59f-76b4-42c7-8be5-7f91d92deac9
-- title:
--   Renyi entropy is the negative inverse-q derivative of free energy
-- statement:
--   Let $H$ be a self-adjoint complex matrix on a nonzero finite-dimensional space and let $k>0$. For $u>0$, set $Z_H(k,u)=\operatorname{tr}\exp(-H/(ku))$, $\rho_H(k,u)=\exp(-H/(ku))/Z_H(k,u)$, and $F_H(k,u)=-ku\ln Z_H(k,u)$. Define $S_q^k(\rho)=k\ln\operatorname{tr}(\rho^q)/(1-q)$ using spectral powers and natural logarithms. For a real function $f$, define its difference quotient $D_a f(x)=(f(ax)-f(x))/(ax-x)$ when $ax\ne x$. For every reference temperature $T>0$ and real entropy order $q>0$, $q\ne1$,
--   $$
--   S_q^k\bigl(\rho_H(k,T)\bigr)
--   =-D_{q^{-1}}\bigl(u\mapsto F_H(k,u)\bigr)(T)
--   =-\frac{F_H(k,T/q)-F_H(k,T)}{T/q-T}.
--   $$
--   This is the inverse-order difference-quotient formulation of the free-energy identity. The entropy is evaluated in the original state at $T$, and the comparison temperature is $T/q$.
-- source:
--   Renyi Entropy and Free Energy, arXiv:1102.2098v4, PDF p. 4, Section 2, Eq. (11)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P26

noncomputable section

open Filter

open scoped BigOperators Topology Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P26

open QAlgorithms.Papers.Independent.Support50.P15 (shannonEntropyNats)

open QAlgorithms.ZeroSum (classicalGibbs)

open QAlgorithms.Papers.Independent.Dependency50.P35 (spectralPower)

/-- PDF p.4, Section 2, (11): S_q at the old/reference temperature T equals
minus D_(q inverse) F(T). The comparison temperature is T/q, and the denominator
is nonzero since T > 0, q > 0, and q != 1. This is the variable change specified
immediately below (11), retaining the same H and k throughout. -/
theorem renyi_qInverseDerivative {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (k T q : ℝ) (hk : 0 < k) (hT : 0 < T) (hq : 0 < q) (hqne : q ≠ 1) :
    renyiEntropyWithBoltzmann (thermalGibbs H k T) k q =
      -qDerivative (thermalFreeEnergy H k) q⁻¹ T := by sorry

end QAlgorithms.Papers.Independent.Advance50.P26

end
