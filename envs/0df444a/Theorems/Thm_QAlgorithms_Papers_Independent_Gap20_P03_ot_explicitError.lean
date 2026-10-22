-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_ot_explicitError
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.ot_explicitError
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:22:33.800955+00:00
-- url     : https://prove2.me/theorems/0fccf043-d301-4160-9e3e-0bac7b5dc019
-- title:
--   Unnumbered: explicit finite-parameter sender-security bound
-- statement:
--   Let $n,\ell,q$ be nonnegative integers, $0<\lambda<1/2$, $\lambda'>0$, and $\kappa>0$. Suppose
--   $$q\le(1/4-\lambda-2\lambda'-\kappa)n-2\ell-1.$$
--   For every receiver attack on Figure 1 with at most $q$ coherent qubits immediately before step 3, there is a classical extension $C'$ satisfying the sender-security criterion with error at most
--   $$\tfrac12\,2^{-\kappa n/2}+2\varepsilon+4\varepsilon',\qquad\varepsilon=\exp\!\left(-\frac{\lambda^2n}{32[2-\log_2\lambda]^2}\right),\quad\varepsilon'=2^{-\lambda'n}.$$
--   The criterion compares the unchosen string to uniform conditioned on the chosen string, $C'$, the public transcript, and the receiver's full final quantum view. This is the finite-parameter bound in Appendix A.4.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 20, Unnumbered: explicit finite-parameter sender-security bound

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Appendix A.4, p.20: explicit finite-parameter distance estimate.
The source's gamma*n is re-expressed by the actual integer checkpoint size q. -/
theorem ot_explicitError (n ell q : ℕ) (lambda lambdaPrime kappa : ℝ)
    (hlambda : 0 < lambda) (hlambdaHalf : lambda < 1/2)
    (hlambdaPrime : 0 < lambdaPrime) (hkappa : 0 < kappa)
    (hmemory : (q:ℝ) ≤ (1/4-lambda-2*lambdaPrime-kappa)*n - 2*ell - 1) :
    OTSenderSecure n ell q
      ((1/2:ℝ)*Real.rpow 2 (-kappa*n/2) + 2*bb84Error n lambda +
        4*Real.rpow 2 (-lambdaPrime*n)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
