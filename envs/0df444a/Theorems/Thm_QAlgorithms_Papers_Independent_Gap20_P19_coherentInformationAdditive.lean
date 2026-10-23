-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_coherentInformationAdditive
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.coherentInformationAdditive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:50:28.445084+00:00
-- url     : https://prove2.me/theorems/7d7f1aeb-7bef-4558-ab54-b26e11ffea55
-- title:
--   A.2: coherent-information subadditivity and channel additivity (72)
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $U,V$ be isometric dilations of two degradable channels $\Phi,\Psi$. Write $I_c(\Phi,\rho)=S[\Phi(\rho)]-S[\Phi^C(\rho)]$ and $I_c(\Phi)=\max_\rho I_c(\Phi,\rho)$ over all density matrices. For every joint input state $\rho_{AA'}$, with its computed marginals $\rho_A,\rho_{A'}$,
--   $$I_c(\Phi\otimes\Psi,\rho_{AA'})\le I_c(\Phi,\rho_A)+I_c(\Psi,\rho_{A'}).$$
--   Moreover $I_c(\Phi\otimes\Psi)=I_c(\Phi)+I_c(\Psi)$ and $I_c(\Phi^{\otimes m})=mI_c(\Phi)$ for every nonnegative integer $m$, with the scalar empty tensor at $m=0$.
--
--   This is information additivity, without asserting an additional operational coding theorem.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 4, A.2: coherent-information subadditivity and channel additivity (72)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

/-- Appendix A.2, PDF pp.4,26, (72): all joint inputs, different degradable
channels, optimized equality, and every tensor power. Supremum sets are nonempty
and bounded for these nonzero finite systems and isometric channels. -/
theorem coherentInformationAdditive [Nonempty A] [Nonempty B] [Nonempty E]
    [Nonempty A2] [Nonempty B2] [Nonempty E2]
    (U : Matrix (B × E) A ℂ) (V : Matrix (B2 × E2) A2 ℂ)
    (hU : IsDegradable U) (hV : IsDegradable V) :
    (∀ rho : Matrix (A × A2) (A × A2) ℂ, IsDensityMatrix rho →
      coherentAt (tensorDilation U V) rho ≤
        coherentAt U (traceRight rho)+coherentAt V (traceLeft rho)) ∧
    maximumCoherentInformation (tensorDilation U V) =
      maximumCoherentInformation U+maximumCoherentInformation V ∧
    (∀ m : ℕ, maximumCoherentInformation (dilationPower U m) =
      (m : ℝ)*maximumCoherentInformation U) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
