-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_ccq_entropy_key_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.ccq_entropy_key_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:26:39.497843+00:00
-- url     : https://prove2.me/theorems/59861ac1-ae41-4415-aaac-048c70303691
-- title:
--   Unnumbered key lower bound for a ccq state, Eq.17
-- statement:
--   Let $\rho_{ABE}$ be a density matrix on three positive finite-dimensional registers, classical in the specified computational bases of $A$ and $B$. Eve's extension is this particular $E$, and $S$ denotes von Neumann entropy in bits. Then the operational forward extraction capacity of this fixed ccq source satisfies
--
--   $$K_{\to}(\rho_{ABE})\ge I(A:B)_{\rho_{AB}}-S(\rho_E).$$
--
--   Here $\rho_{AB}$ and $\rho_E$ are the actual partial traces of $\rho_{ABE}$, and $I(A:B)=S(\rho_A)+S(\rho_B)-S(\rho_{AB})$. The accepted capacity evaluates finite local measurements and forward authenticated public discussion on independent copies, includes the transcript with Eve, and lets the correctness and secrecy errors tend to zero. The bound remains valid when its right side is negative. It specializes Eq. (3) to the ccq setting; it is not the bipartite key capacity of the separable classical marginal.
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 3, Unnumbered key lower bound for a ccq state, Eq.17

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF p.3, Eq.(17): one-way extraction from a FIXED ccq source and its actual
Eve marginal. It is not bipartite key distillation of the separable AB marginal.
Negative right sides remain legitimate lower bounds. -/
theorem ccq_entropy_key_lower_bound {a b e : ℕ} (ha : 0 < a) (hb : 0 < b)
    (he : 0 < e) (rho : Op (Fin a × (Fin b × Fin e)))
    (hrho : IsDensityMatrix rho) (hccq : IsCCQ rho) :
    Frontier30.P12.quantumMutualInfo (Dependency50.P21.marginalAB rho) -
      vnEntropy (traceLeft (traceLeft rho)) ≤ Frontier30.P12.quantumKeyCapacity rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
