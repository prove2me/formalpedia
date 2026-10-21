-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P46_coherentInformationIdentity
-- name    : QAlgorithms.Papers.Independent.Next46.P46.coherentInformationIdentity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:59:16.323976+00:00
-- url     : https://prove2.me/theorems/030f0f9f-4278-47de-99c2-1e02ac3b254c
-- title:
--   Coherent information equals the private information difference
-- statement:
--   Let $P$ be a probability distribution on a finite nonempty alphabet $X$, allowing zero probabilities, and let $(|\phi_x\rangle^{BE})_x$ be an orthonormal family in finite-dimensional $BE$. Form the coherent source and its dephased version:
--
--   $$
--   |\psi\rangle^{ABE}=\sum_x\sqrt{P(x)}|x\rangle^A|\phi_x\rangle^{BE},\qquad
--   \bar\psi^{XBE}=\sum_xP(x)|x\rangle\!\langle x|^X\otimes|\phi_x\rangle\!\langle\phi_x|^{BE}.
--   $$
--
--   Using the coherent state for quantities involving $A$ and the dephased state for those involving $X$, one has
--
--   $$
--   I_c(A\rangle B)=H(B)-H(AB)=H(B)-H(E)=I(X;B)-I(X;E).
--   $$
--
--   Here $I(C;D)=H(C)+H(D)-H(CD)$, all entropies use base-two logarithms, and zero-weight entropy terms vanish. This identity connects the private and coherent rate calculations without equating the two source states.
-- source:
--   Relating quantum privacy and quantum coherence: an operational approach, arXiv:quant-ph/0307053v1, PDF p. 2, Entropy notation following equation (1)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)

open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

/-- arXiv:quant-ph/0307053v1, PDF p.2: coherent and dephased entropies.
The conditional BE vectors are orthonormal, and zero Schmidt weights are allowed.
Purity and the entropy identity are conclusions of the source model, not assumptions. -/
theorem coherentInformationIdentity {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    [Nonempty X] [Nonempty B] [Nonempty E]
    (p : X → ℝ) (hp : IsLaw p) (phi : X → Vec (B × E))
    (hphi : Orthonormal ℂ phi) :
    let psi := WithLp.toLp 2 (fun z : X × (B × E) => (Real.sqrt (p z.1) : ℂ) * phi z.1 z.2)
    let rho := pureDensity psi
    let barRho := dephased p phi
    coherentInfo (marginalAB rho) =
      vnEntropy (traceRight (traceLeft rho)) - vnEntropy (traceLeft (traceLeft rho)) ∧
    vnEntropy (traceRight (traceLeft rho)) - vnEntropy (traceLeft (traceLeft rho)) =
      quantumMutualInfo (marginalAB barRho) - quantumMutualInfo (marginalAE barRho) := by sorry

end QAlgorithms.Papers.Independent.Next46.P46

end
