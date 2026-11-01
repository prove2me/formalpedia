-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P96_unentangled_single_shot
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P96.unentangled_single_shot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:48:25.346151+00:00
-- url     : https://prove2.me/theorems/2682ade1-0988-4be2-ad47-834bff187018
-- title:
--   Optimal unentangled single-shot test and four probabilities
-- statement:
--   Work in the retained vacuum/single-photon model, on a signal space with vacuum $|\mathrm{vac}\rangle$ and $d\ge1$ orthogonal single-photon modes. Let $b\ge0$ be the background probability per mode, with $db\le1$, and let $0\le\eta\le1$ be the reflection probability. Set
--   $$
--   \rho_0=(1-db)|\mathrm{vac}\rangle\langle\mathrm{vac}|+b\sum_{k=1}^d|k\rangle\langle k|.
--   $$
--
--   Let $|\psi\rangle$ be any unit single-photon vector with zero vacuum amplitude, let $P_\psi=|\psi\rangle\langle\psi|$, and put $\rho_1=(1-\eta)\rho_0+\eta P_\psi$.
--   With equal prior probabilities of absence and presence, the binary measurement $\{P_\psi,I-P_\psi\}$, guessing present on yes, minimizes the error among all binary POVMs. Its four conditional probabilities are
--   $$
--   \begin{aligned}
--   p(\mathrm{no}\mid0)&=1-b,&p(\mathrm{yes}\mid0)&=b,\\
--   p(\mathrm{no}\mid1)&=(1-b)(1-\eta),&
--   p(\mathrm{yes}\mid1)&=b(1-\eta)+\eta .
--   \end{aligned}
--   $$
--   The labels $0,1$ denote object absent and present. This gives both the decision measurement and its complete conditional law, without claiming uniqueness when the states coincide.
-- source:
--   Quantum Illumination, arXiv:0803.2022v2, PDF p. 3, Optimal unentangled single-shot test and four conditional probabilities (2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P96

noncomputable section

open Filter

open scoped BigOperators Topology ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P96

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, (2): optimal equal-prior single-shot test and all four conditional
probabilities. Optimality is not uniqueness, including at eta=0. -/
theorem unentangled_single_shot (p : ModelParameters)
    (psi : EuclideanSpace ℂ (Fin p.d)) (hpsi : IsState psi) :
    IsEffect (signalTest psi) ∧
    (∀ M : Matrix (SignalIndex p.d) (SignalIndex p.d) ℂ, IsEffect M →
      binaryError (background p.d p.b) (signalPresent p.b p.eta psi) (signalTest psi) ≤
        binaryError (background p.d p.b) (signalPresent p.b p.eta psi) M) ∧
    effectProb (1 - signalTest psi) (background p.d p.b) = 1 - p.b ∧
    effectProb (1 - signalTest psi) (signalPresent p.b p.eta psi) =
      (1 - p.b) * (1 - p.eta) ∧
    effectProb (signalTest psi) (background p.d p.b) = p.b ∧
    effectProb (signalTest psi) (signalPresent p.b p.eta psi) =
      p.b * (1 - p.eta) + p.eta := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P96

end
