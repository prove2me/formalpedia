-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_quantumRelativeEntropy
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.quantumRelativeEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:25:46.504912+00:00
-- url     : https://prove2.me/theorems/442c25f9-1628-4233-b6f8-e6e98b6a0aaf
-- title:
--   The nearest product density matrix
-- statement:
--   Let $\rho$ be a normalized density matrix on $n\ge2$ labelled local Hilbert spaces of nonzero finite dimensions, with reductions $\rho_i$. With $D_2$ denoting support-aware Umegaki relative entropy divided by $\ln2$,
--   $$T_n(\rho)=D_2(\rho\Vert\bigotimes_i\rho_i)=\min_{\eta_i\text{ density matrices}}D_2(\rho\Vert\bigotimes_i\eta_i).$$
--   The actual reduced states and all candidate products are normalized density matrices. The minimum is attained at $\eta_i=\rho_i$; divergence is infinite when support inclusion fails.
--
--   The equality and minimizing product are explicit, rather than an existence-only substitute.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 10, §V.B

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P37

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

/-- §V.B, PDF p.10: nearest product density, in bits, attained at the
actual reduced states. Infinite divergence on support violations is retained.
Product normalization and lawMarginal normalization are conclusions. -/
theorem quantumRelativeEntropy {n : ℕ} (hn : 2 ≤ n) (s : FiniteState n) :
    (∀ i, IsDensityMatrix (localDensity s i)) ∧
    IsDensityMatrix (labelledProductDensity (localDensity s)) ∧
    quantumKL s.rho (labelledProductDensity (localDensity s)) = ENNReal.ofReal (qValue .total s) ∧
    ∀ eta : (i : Fin n) → Matrix (Fin (s.dims i)) (Fin (s.dims i)) ℂ,
      (∀ i, IsDensityMatrix (eta i)) →
      IsDensityMatrix (labelledProductDensity eta) ∧
      ENNReal.ofReal (qValue .total s) ≤ quantumKL s.rho (labelledProductDensity eta) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
