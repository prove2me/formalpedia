-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_holevo_remainder
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.holevo_remainder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:57:48.442006+00:00
-- url     : https://prove2.me/theorems/3320b60a-bbdf-43dc-9ebd-956008c885f2
-- title:
--   Consequence 29
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Assume the universal inequality (6.24) with its original positive-definite-state and strict-CPTP hypotheses. Let $p_x,\rho_B^x$ be any finite normalized ensemble, including singular states, and let $\{|\varphi_y\rangle\}$ be an arbitrary finite rank-one POVM on $B$. Write $\bar\rho_B=\sum_xp_x\rho_B^x$ and let $\mathcal E$ be (6.59), completed on zero-probability outcomes by preparing $\bar\rho_B$. Then
--
--   $$I(X;B)-I(X;Y)\ge-2\log\sum_xp_x\sqrt{F(\rho_B^x,\mathcal E(\rho_B^x))}.$$
--
--   Here $I(X;B)=H(\bar\rho)-\sum_xp_xH(\rho^x)$, and $I(X;Y)$ is the classical mutual information of $p_x\langle\varphi_y|\rho^x|\varphi_y\rangle$. The same computed EB channel acts on every branch. The singular application is a conclusion obtained by support continuity, not an extra premise.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 29, Consequence 29

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P56

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P56

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw entropy average holevo)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint petz extendedLog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartiteProduct)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Advance50.P25 (renyiEntropyNats)

variable {A B C D E X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype X]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty E] [Nonempty X]

open scoped Matrix.Norms.L2Operator

/-- arXiv:1410.1443v3, PDF pp.29–31, Consequence 29, (6.58)–(6.59).
The same EB map is used on every ensemble element. Singular ensembles are
allowed; the universal bound's support extension is part of this consequence. -/
theorem holevo_remainder (recovery : RecoveryRemainder)
    (p : X → ℝ) (hp : IsLaw p) (rho : X → Op B)
    (hrho : ∀ x, IsDensityMatrix (rho x)) (m : ℕ) (hm : 0 < m)
    (phi : Fin m → EuclideanSpace ℂ B) (hphi : KetPOVM phi) :
    let bar := average rho p
    let EB := measurementRecovery bar bar phi
    let joint : X × Fin m → ℝ := fun xy => p xy.1 * effectProb (pureDensity (phi xy.2)) (rho xy.1)
    let classicalMI : ℝ := ∑ x, ∑ y, joint (x,y) * Real.log (joint (x,y) /
      ((∑ z, joint (x,z)) * (∑ z, joint (z,y))));
    -(2 * extendedLog (∑ x, p x * Real.sqrt (squaredFidelity (rho x) (EB (rho x))))) ≤
      ((holevo p rho - classicalMI : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
