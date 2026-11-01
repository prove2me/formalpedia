-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_pure_discord_formula
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.pure_discord_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:53:14.572985+00:00
-- url     : https://prove2.me/theorems/1afa7216-e2bd-411d-851a-aedbe2d12155
-- title:
--   Proposition 21
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $|\psi\rangle_{AB}$ be normalized and $\alpha\in(0,1)\cup(1,2]$. For a finite rank-one POVM $\sum_x|\varphi_x\rangle\langle\varphi_x|=I_A$, set $z_x=\langle\varphi_x|\psi\rangle$, $p_x=\|z_x\|^2$, and $\xi_x=z_x/\sqrt{p_x}$ whenever $p_x>0$. Then
--
--   $$D_\alpha(\bar A;B)_\psi=\inf_{\varphi}\frac{\alpha}{\alpha-1}\log\sum_{x:p_x>0}p_x\langle\xi_x|\psi_B^{1-\alpha}|\xi_x\rangle^{1/\alpha}.$$
--
--   The prefactor remains inside the infimum and no normalization is imposed on the POVM kets. This evaluates pure-state discord through the computed conditional kets.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 20, Proposition 21

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

/-- arXiv:1410.1443v3, PDF pp.20–21, Proposition 21, (5.27)–(5.28). -/
theorem pure_discord_formula (a : ℝ) (ha : DPOrder a)
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1) :
    renyiDiscord a (pureDensity psi) = sInf {v : EReal |
      ∃ m : ℕ, 0 < m ∧ ∃ phi : Fin m → EuclideanSpace ℂ A,
        KetPOVM phi ∧ v = (pureDiscordObjective a psi phi : EReal)} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
