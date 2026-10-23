-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_nearIdentityNeither
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.nearIdentityNeither
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:48:40.135726+00:00
-- url     : https://prove2.me/theorems/d08f61bb-6204-44d4-ba6a-6d09a5387b19
-- title:
--   §7: qutrit nondegradable channels arbitrarily near identity
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Set $\varepsilon_n=1/(n+4)$ for $n\ge0$ and
--   $$T_n(\rho)=(1-2\varepsilon_n)\rho+\varepsilon_nX\rho X^\dagger+\varepsilon_nZ\rho Z^\dagger$$
--   on qutrits. Every $T_n$ is CPTP, has Choi rank three, and is neither degradable nor antidegradable. Also $2\varepsilon_n\to0$, and for every matrix unit $E_{ij}$ and every output entry $(k,l)$, $(T_n(E_{ij}))_{kl}\to(E_{ij})_{kl}$.
--
--   This makes the source's arbitrarily-near-identity conclusion precise by entrywise convergence, without inventing a diamond-distance constant.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 23, §7: qutrit nondegradable channels arbitrarily near identity

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

/-- Section 7, PDF p.23: an explicit sequence of rank-three qutrit channels,
neither class, converging entrywise on all matrix units to the identity. -/
theorem nearIdentityNeither :
    let eps : ℕ → ℝ := fun n => 1/((n : ℝ)+4)
    let N : ℕ → Superop (Fin 3) (Fin 3) := fun n => threeWeyl (1-2*eps n) (eps n) (eps n)
    (∀ n, IsChannel (N n) ∧ (choi (N n)).rank = 3 ∧
      ¬ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (N n) ∧ IsDegradable witness) ∧ ¬ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (N n) ∧ IsAntidegradable witness)) ∧
    Tendsto (fun n => 2*eps n) atTop (nhds 0) ∧
    (∀ i j k l : Fin 3, Tendsto (fun n => N n (Matrix.single i j 1) k l)
      atTop (nhds ((Matrix.single i j 1 : Matrix (Fin 3) (Fin 3) ℂ) k l))) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
