-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_timeReversal
-- name    : QAlgorithms.Papers.Independent.Gap48.P20.timeReversal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:04:42.970778+00:00
-- url     : https://prove2.me/theorems/cb463232-8c15-4684-b93d-4fb91caf99c3
-- title:
--   Reversible optimal implementations and cost symmetry
-- statement:
--   For a normalized pure state $|\psi\rangle^{ACBR}$ on nonzero finite registers, define $Q_* = I(C;R\mid B)/2$ and $E_*=[I(C;A)-I(C;B)]/2$, using entropy in bits. Let $\psi^{\mathrm{swap}}$ denote the same state with the sender and receiver side information $A,B$ exchanged. Then
--   $$
--   I(C;R\mid B)=I(C;R\mid A),\qquad Q_*(\psi^{\mathrm{swap}})=Q_*(\psi),\qquad E_*(\psi^{\mathrm{swap}})=-E_*(\psi).
--   $$
--   There is a family of coherent protocols attaining $(Q_*,E_*)$: for every positive error tolerance and rate slack, all sufficiently large positive blocklengths have local unitaries with explicit pure input ancillas and retained output work registers. Their complete output, including the source, final Bell pairs, and pure output work, approaches the ideal pure target in full trace norm. Reversing these same local unitaries and sending the same message back approaches the original source, Bell pairs, and input work with the same vanishing-error requirement. The forward net Bell consumption approaches $E_*$; reversal exchanges the Bell banks and attains $(Q_*,-E_*)$ for transferring $C$ back.
--
--   This statement includes zero entanglement cost. It expresses operational reversibility, including work registers, rather than only the entropy identity.
-- source:
--   The operational meaning of quantum conditional information, arXiv:quant-ph/0612050v2, PDF p. 2, time-reversal

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P20

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Self-duality under time reversal, PDF pp.2–4: CMI duality, opposite ebit
cost, and actual reversible coherent implementations at the corner. -/
theorem timeReversal {A C B R : Type*}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty C] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (hpsi : IsState psi) :
    2 * quantumCost psi = 2 * quantumCost (swappedSource psi) ∧
    redistributionEntanglementRate (swappedSource psi) = -redistributionEntanglementRate psi ∧
    ReversiblyAchievable psi (quantumCost psi) (redistributionEntanglementRate psi) ∧
    RedistributionAchievable (swappedSource psi) (quantumCost psi) (-redistributionEntanglementRate psi) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P20

end
