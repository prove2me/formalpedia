-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_public_discussion_reduction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.public_discussion_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:16:37.959417+00:00
-- url     : https://prove2.me/theorems/b5b41b83-7b38-4307-b737-9d3a00c9c462
-- title:
--   §IV-E-III, unnumbered reduction in required public discussion
-- statement:
--   Let $S,X,Y,Z$ be finite nonempty alphabets and let $W(x,y,z\mid s)$ be a normalized discrete memoryless broadcast channel. All entropies and information quantities are in bits. For an input law $p$, information quantities below use exactly the induced law $p(s)W(x,y,z\mid s)$.
--
--   For a fixed input law, the public-rate thresholds of source emulation and the hybrid reliability construction satisfy
--   $$H(X,S\mid Y)-H(X\mid Y,S)=H(S\mid Y)\ge0.$$
--   For every $R_\Phi>H(X\mid Y,S)$ there is a nonnegative $R_M$ with $R_\Phi-R_M>H(X\mid Y,S)-I(S;Y)$, so both hybrid reliability conditions hold. The threshold reduction is strict only if $H(S\mid Y)>0$.
--
--   This compares sufficient thresholds of two constructions and asserts no universal public-discussion converse.
--   More precisely, for every $R_K\ge0$ below $I(X,S;Y)-I(X,S;Z)$ and every $R_\Phi>H(X\mid Y,S)$, there is $R_M\ge0$ such that
--   $$R_K+R_\Phi-H(X\mid Z,S)+I(S;Z)<R_M<R_\Phi-H(X\mid Y,S)+I(S;Y).$$
--   Both exponents at these rates are positive, and $R_K$ is strongly achievable.
--
--   The witnessing code sequence uses exactly the specified public rate $R_\Phi$ and the very same nonnegative message rate $R_M$ chosen in the displayed interval, so its public-discussion budget is retained in the operational conclusion.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 9, §IV-E-III, unnumbered reduction in required public discussion

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

/-- PDF p.9: construction-specific thresholds differ by H(S|Y). The smaller
threshold admits a nonnegative excitation-rate choice meeting reliability AND
secrecy for each nonnegative key rate strictly below the information advantage.
The witnessing codes use this very public rate and chosen excitation rate;
this is not a converse against all protocols below that threshold. -/
theorem public_discussion_reduction (W : DMBC S X Y Z) (p : S → ℝ) (hp : IsLaw p) :
    let q := excitationJointMass W p
    condEntropy q (fun o => (obsX o, obsS o)) obsY -
      condEntropy q obsX (fun o => (obsY o, obsS o)) = condEntropy q obsS obsY ∧
    condEntropy q obsX (fun o => (obsY o, obsS o)) ≤
      condEntropy q (fun o => (obsX o, obsS o)) obsY ∧
    (∀ RK RP : ℝ, 0 ≤ RK → RK < advantage W p →
      condEntropy q obsX (fun o => (obsY o, obsS o)) < RP →
      ∃ RM : ℝ, 0 ≤ RM ∧
        RK + RP - condEntropy q obsX (fun o => (obsZ o, obsS o)) +
          observationMutualInfoBits q obsS obsZ < RM ∧
        RM < RP - condEntropy q obsX (fun o => (obsY o, obsS o)) +
          observationMutualInfoBits q obsS obsY ∧
        0 < reliabilityExponent W p RP RM ∧
        0 < secrecyExponent W p RK RP RM ∧ StrongAchievableAt W RK RP RM) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
