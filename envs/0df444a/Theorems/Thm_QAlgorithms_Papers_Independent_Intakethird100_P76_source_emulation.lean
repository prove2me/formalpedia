-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_source_emulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.source_emulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:15:58.774703+00:00
-- url     : https://prove2.me/theorems/b8cfcae6-8b6c-4679-a43b-ae4b52034496
-- title:
--   §IV-E-III, source-emulation rate conditions (38)–(40)
-- statement:
--   Let $S,X,Y,Z$ be finite nonempty alphabets and let $W(x,y,z\mid s)$ be a normalized discrete memoryless broadcast channel. All entropies and information quantities are in bits. For an input law $p$, information quantities below use exactly the induced law $p(s)W(x,y,z\mid s)$.
--
--   For a fixed input law and nonnegative key and public rates, substituting $R_M=H(S)$ into (28) and (29) gives the equivalent conditions
--   $$R_\Phi>H(X,S\mid Y),\qquad R_{\rm SK}+R_\Phi<H(X,S\mid Z).$$
--   There exists a nonnegative public rate satisfying both if and only if
--   $$R_{\rm SK}<H(X,S\mid Z)-H(X,S\mid Y)=I(X,S;Y)-I(X,S;Z).$$
--
--   This describes source emulation at the rate-inequality level without identifying different exponent formulas.
--   Under (38) and (39), the reliability exponent at $R_M=H(S)$ and the secrecy exponent are both strictly positive and the rate is strongly achievable. Every nonnegative rate below the displayed information difference is strongly achievable after choosing a public rate.
--
--   Under (38) and (39), the witnessing code sequence has excitation rate exactly $H(S)$ and public rate exactly the specified $R_\Phi$. The final rate-only consequence still quantifies over a choice of public rate.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 8, §IV-E-III, source-emulation rate conditions (38)–(40)

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

/-- PDF p.8, (38)--(40): substitute R_M=H(S), retain both rate conditions
their exact public-rate elimination, positive exponents and strong achievability
at the specified public rate and excitation rate H(S);
no equality of exponent functions. -/
theorem source_emulation (W : DMBC S X Y Z) (p : S → ℝ) (hp : IsLaw p)
    (RK RP : ℝ) (hK : 0 ≤ RK) (hP : 0 ≤ RP) :
    let q := excitationJointMass W p
    ((condEntropy q obsX (fun o => (obsY o, obsS o)) - observationMutualInfoBits q obsS obsY <
      RP - observationEntropyBits q obsS) ↔ condEntropy q (fun o => (obsX o, obsS o)) obsY < RP) ∧
    ((RK + RP - observationEntropyBits q obsS <
      condEntropy q obsX (fun o => (obsZ o, obsS o)) - observationMutualInfoBits q obsS obsZ) ↔
      RK + RP < condEntropy q (fun o => (obsX o, obsS o)) obsZ) ∧
    ((∃ r : ℝ, 0 ≤ r ∧ condEntropy q (fun o => (obsX o, obsS o)) obsY < r ∧
      RK + r < condEntropy q (fun o => (obsX o, obsS o)) obsZ) ↔
      RK < advantage W p) ∧
    ((condEntropy q (fun o => (obsX o, obsS o)) obsY < RP ∧
      RK + RP < condEntropy q (fun o => (obsX o, obsS o)) obsZ) →
      0 < reliabilityExponent W p RP (observationEntropyBits q obsS) ∧
      0 < secrecyExponent W p RK RP (observationEntropyBits q obsS) ∧
      StrongAchievableAt W RK RP (observationEntropyBits q obsS)) ∧
    (RK < advantage W p → StrongAchievable W RK) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
