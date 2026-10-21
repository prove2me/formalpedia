-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_cartesian_heralded_perfect
-- name    : QAlgorithms.Papers.Independent.Next46.P29.cartesian_heralded_perfect
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:24:04.471966+00:00
-- url     : https://prove2.me/theorems/43eb670f-5769-44b4-8cd1-e6769fb1f225
-- title:
--   Heralded Cartesian recovery by rejecting the top spin
-- statement:
--   Use the actual canonical integer-spin token with cutoff $L\ge0$, normalized SU(2) Haar encoding $\mathcal E_L$, and fixed covariant recovery $\mathcal R_L$. Measure the actual total-spin projectors $\Pi_t$ for $J=t+1/2$, and accept exactly $t=0,\ldots,L-1$. On arbitrary joint operators let $\mathcal R_{\mathrm{acc}}(Y)=\sum_{t=0}^{L-1}\mathcal R_L(\Pi_tY\Pi_t)$. This is a completely positive trace-nonincreasing operation, and
--
--   $$\mathcal R_{\mathrm{acc}}\mathcal E_L(\rho)=\frac{2L}{2L+3}\rho,\qquad\operatorname{Tr}\mathcal R_{\mathrm{acc}}\mathcal E_L(\rho)=\frac{2L}{2L+3}$$
--
--   for every qubit density operator. The accepted range is empty at $L=0$. This states achieved success, without an optimality claim.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 14, §V.B: heralded Cartesian decoding, Eq.(93)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.14, Eq.(93): rejecting the actual top-spin sector achieves exact
heralded recovery with probability `2 j_R/(2 j_R+3)`. This is an achieved
probability, not an optimization over all accepted operations. -/
theorem cartesian_heralded_perfect (L : ℕ) :
    IsSubchannel (cartesianAccepted L) ∧
    ∀ rho, IsDensityMatrix rho →
      cartesianAccepted L (cartesianEncoding L rho) =
        ((2 * (L : ℝ)) / (2 * L + 3) : ℂ) • rho ∧
      (cartesianAccepted L (cartesianEncoding L rho)).trace.re =
        (2 * (L : ℝ)) / (2 * L + 3) := by sorry

end QAlgorithms.Papers.Independent.Next46.P29

end
