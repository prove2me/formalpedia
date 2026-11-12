-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_rate_decomposition
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.rate_decomposition
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T09:11:42.924988+00:00
-- url     : https://prove2.me/theorems/fd64c754-c411-4003-b93a-67544a9e2934
-- title:
--   §III, unnumbered source/channel rate decomposition (15)–(17)
-- statement:
--   Let $S,X,Y,Z$ be finite nonempty alphabets and let $W(x,y,z\mid s)$ be a normalized discrete memoryless broadcast channel. All entropies and information quantities are in bits. For an input law $p$, information quantities below use exactly the induced law $p(s)W(x,y,z\mid s)$.
--
--   For every normalized input distribution define $R_{\rm ch}=I(S;Y)-I(S;Z)$ and $R_{\rm src}=I(X;Y\mid S)-I(X;Z\mid S)$. Then
--   $$I(X,S;Y)-I(X,S;Z)=R_{\rm ch}+R_{\rm src}.$$
--   Neither summand is assumed nonnegative, and degradedness is unnecessary.
--
--   The identity separates the channel and residual-source contributions.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 5, §III, unnumbered source/channel rate decomposition (15)–(17)

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

/-- PDF p.5, (15)--(17): no degradedness or sign restrictions. -/
theorem rate_decomposition (W : DMBC S X Y Z) (p : S → ℝ) (hp : IsLaw p) :
    advantage W p = channelRate W p + residualSourceRate W p := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
