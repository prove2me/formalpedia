-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_cowm1_information
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.cowm1_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:34:06.281828+00:00
-- url     : https://prove2.me/theorems/e45cbe04-118c-4b94-9d9f-980d8efedaa6
-- title:
--   COWm1 2PA information with the public alignment flag
-- statement:
--   Work in the source's normalized leading-order ancilla model for $\mu t\ll1$, retaining Bob's vacuum and single-photon sectors. Fix one repeated one-pulse or disjoint-pair strategy; the same ancilla data are used in each copy. All ancillary vectors are unit vectors, all stated vacuum overlaps are complex equalities, and every specified conditional visibility is tested separately and equals $V\in[0,1]$. The bit error parameter is $Q\in[0,1]$ when independently applicable. Bits are uniform; Eve retains the public pairing flag and quantum memory. The signed one-way Devetak–Winter expression assumes ideal error correction and the source's per-slot apparatus prefactors. This is an exact statement about this normalized model, without a finite-loss realization or remainder assertion.
--
--   For $\mu\ge0$ use all COW vacuum and visibility constraints and add the vacuum-input overlaps, so $\langle v_x,v_y\rangle=e^{-\mu d_H(x,y)/2}$ for all four occupancy pairs. Construct four orthogonal error flags in extra dimensions. For a bit crossing attacked pairs, the input pairs are $(j,1-a)$ and $(a,k')$, with independent outer occupancies $j,k'$. The conditional states are the four equally weighted product projectors in (24),(25); the Alice/Bob marginals then mix correct and error branches with weights $1-Q,Q$. In particular, the correct ensembles are $\rho_4^{00}=\frac14\sum_{j,k'}P_{p_{j\mu}^{01}\otimes v_{0k'}}$ and $\rho_4^{11}=\frac14\sum_{j,k'}P_{v_{j0}\otimes p_{\mu k'}^{10}}$.
--
--   Writing $c=|\langle p_{\mu0}^{10},p_{0\mu}^{01}\rangle|$, the equiprobable public alignment cases give normalized marginals and
--
--   $$\chi_{AE}=\chi_{BE}=Q+\frac{1-Q}{2}\{h((1+c)/2)+\chi(\rho_4^{00},\rho_4^{11})\},\quad r_0=\frac\mu2[1-h(Q)-\chi_{AE}].$$
--
--   The unflagged attack leakages cannot exceed this extension’s values. This retains the crossing-state mixtures and Eve’s alignment information.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 6, IV B, Eqs.(17)–(27): COWm1 2PA information and rate coefficient

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P92

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P92

open QAlgorithms.Papers.Independent.Information100.P21 (Vec tensor)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

open QAlgorithms.Papers.Independent.Frontier18.P14
  (Fock coherentPair coherentPairCoefficients passiveApply passiveCoefficients
   fockReducedFirst reducedSecond coherentCoefficient)

/-- PDF pp.6–7, (17)–(27): COWm1 crossing-pair states and equal alignment-flag
averages. Orthogonal flags are a maximizing extension, not a restriction on the
original attack. The signed rate is the leading-order coefficient times t eta. -/
theorem cowm1_information {I : Type*} [Fintype I] [DecidableEq I]
    (A : PairData I) (mu V Q : ℝ) (hmu : 0 ≤ mu)
    (hV : V ∈ Set.Icc (0:ℝ) 1) (hQ : Q ∈ Set.Icc (0:ℝ) 1)
    (hA : CowValid A mu V true) :
    CowValid (flaggedPair A) mu V true ∧
    (∀ a, weightedAncillaTrace (crossCow (flaggedPair A) Q a) = 1 ∧
      weightedAncillaTrace (crossCowB (flaggedPair A) Q a) = 1 ∧ weightedAncillaTrace (crossCorrect A a) = 1) ∧
    cowm1Info (flaggedPair A) Q false = cowm1Leak A Q ∧
    cowm1Info (flaggedPair A) Q true = cowm1Leak A Q ∧
    cowm1Info A Q false ≤ cowm1Leak A Q ∧ cowm1Info A Q true ≤ cowm1Leak A Q ∧
    dw (mu/2) Q (cowm1Info (flaggedPair A) Q false)
      (cowm1Info (flaggedPair A) Q true) =
      mu/2*(1-QAlgorithms.binEntropy2 Q-cowm1Leak A Q) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
