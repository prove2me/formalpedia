-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_bipartiteMeasuredCorrelation
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.bipartiteMeasuredCorrelation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:28:34.144478+00:00
-- url     : https://prove2.me/theorems/f76e34b7-ffbf-4c3d-9c26-3dc738952735
-- title:
--   Bipartite extraction bound attained in a Schmidt basis
-- statement:
--   Let $\rho=|\psi\rangle\langle\psi|$ be a normalized bipartite pure state of nonzero finite local dimensions. Consider any finite adaptive local-instrument protocol, with public transcript $\tau$ heard by Eve, ending in classical variables $X,Y$. Then
--   $$\sum_\tau p(\tau)I(X:Y\mid\tau)\le S(\rho_A)=S(\rho_B).$$
--   There exist a Schmidt expansion with orthonormal local vectors and normalized nonnegative Schmidt weights, and local Schmidt measurements without public communication, whose equal classical outputs have mutual information exactly $S(\rho_A)$.
--
--   This asserts achievability, not uniqueness of the optimal measurement.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 12, §V.E, (70),(71)

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

/-- §V.E, PDF pp.11--12, (70),(71): pure bipartite measured information,
conditioned on the full transcript, is bounded by either local entropy.
A Schmidt measurement without messages attains the bound. No uniqueness claim. -/
theorem bipartiteMeasuredCorrelation (s : FiniteState 2)
    (hpure : QAlgorithms.Papers.Independent.Information100.P08.IsPure s.rho) :
    qH s {0} = qH s {1} ∧
    (∀ out : List (ℝ × FiniteState 2), QLOPC s out →
      (∀ z ∈ out, 0 < z.1 → IsDiagonalOutput z.2) →
      (out.map fun z => z.1 * lawCMI (readout z.2) {0} {1} ∅).sum ≤ qH s {0}) ∧
    (∃ (k : ℕ) (w : Fin k → ℝ)
      (u : Fin k → EuclideanSpace ℂ (Fin (s.dims 0)))
      (v : Fin k → EuclideanSpace ℂ (Fin (s.dims 1))),
      0 < k ∧ IsSchmidtExpansion s k w u v ∧
      ∃ t : FiniteState 2, IsDiagonalOutput t ∧ readout t = schmidtLaw w ∧
        QLOPC s [(1,t)] ∧ lawCMI (readout t) {0} {1} ∅ = qH s {0}) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
