-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_source_specialization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.source_specialization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:14:46.229275+00:00
-- url     : https://prove2.me/theorems/fe8c5ae2-c8dc-433a-afab-723809f291c0
-- title:
--   §IV-E-II, source-model rate conditions (36)–(37)
-- statement:
--   Let $S,X,Y,Z$ be finite nonempty alphabets and let $W(x,y,z\mid s)$ be a normalized discrete memoryless broadcast channel. All entropies and information quantities are in bits. For an input law $p$, information quantities below use exactly the induced law $p(s)W(x,y,z\mid s)$.
--
--   Set $S$ to a singleton and $R_M=0$. For any nonnegative key and public rates the pair of reliability conditions (27)--(28) is equivalent to
--   $$R_\Phi>H(X\mid Y),$$
--   and the secrecy condition (29) is equivalent to
--   $$R_{\rm SK}+R_\Phi<H(X\mid Z).$$
--
--   These are exactly the paper's rate-condition specializations, rather than a claim about empty alphabets or a new attribution of the background coding theorems.
--   Under both strict conditions, the specialized reliability and secrecy exponents are strictly positive, and the secret-key rate is strongly achievable.
--
--   The witnessing code sequence has excitation rate exactly zero and public rate exactly the specified $R_\Phi$, with the same ceiling convention at every positive blocklength.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 8, §IV-E-II, source-model rate conditions (36)–(37)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P76

namespace QAlgorithms.Papers.Independent.Intakethird100.P76

noncomputable section

open scoped BigOperators

open Filter Set

attribute [local instance] Classical.propDecidable

-- Exact pinned primitives, inspected at their definitions before reuse.

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

variable {S X Y Z : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
  [Nonempty S] [Nonempty X] [Nonempty Y] [Nonempty Z]

variable {n u w : ℕ}

/-- PDF p.8, (36)--(37): S is a singleton, not an empty alphabet.
Both specialized rate conditions, positive exponents and strong achievability
at the specified public rate and zero excitation rate
are retained without attributing the cited
background Slepian--Wolf or privacy-amplification theorems to this paper. -/
theorem source_specialization (W : DMBC Unit X Y Z) (RK RP : ℝ)
    (hK : 0 ≤ RK) (hP : 0 ≤ RP) :
    let p : Unit → ℝ := fun _ => 1
    ((condEntropy (excitationJointMass W p) obsX (fun o => (obsY o, obsS o)) < RP ∧
      condEntropy (excitationJointMass W p) obsX (fun o => (obsY o, obsS o)) -
        observationMutualInfoBits (excitationJointMass W p) obsS obsY < RP - 0) ↔
      condEntropy (excitationJointMass W p) obsX obsY < RP) ∧
    ((RK + RP - 0 < condEntropy (excitationJointMass W p) obsX (fun o => (obsZ o, obsS o)) -
      observationMutualInfoBits (excitationJointMass W p) obsS obsZ) ↔ RK + RP < condEntropy (excitationJointMass W p) obsX obsZ) ∧
    ((condEntropy (excitationJointMass W p) obsX obsY < RP ∧
      RK + RP < condEntropy (excitationJointMass W p) obsX obsZ) →
      0 < reliabilityExponent W p RP 0 ∧ 0 < secrecyExponent W p RK RP 0 ∧
      StrongAchievableAt W RK RP 0) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
