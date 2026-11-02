-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_strong_degraded
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.strong_degraded
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:13:59.221195+00:00
-- url     : https://prove2.me/theorems/b36c3898-5bd1-4b98-a178-01910f1595fd
-- title:
--   §IV-D, unnumbered strong achievability below degraded capacity (33)
-- statement:
--   Let $S,X,Y,Z$ be finite nonempty alphabets and let $W(x,y,z\mid s)$ be a normalized discrete memoryless broadcast channel. All entropies and information quantities are in bits. For an input law $p$, information quantities below use exactly the induced law $p(s)W(x,y,z\mid s)$.
--
--   Alice draws a uniform finite message $M$, uses a possibly stochastic encoder to excite $n$ channel uses, and observes $(M,X^n)$. A public forward message $\Phi=\phi(M,X^n)$ is visible to Bob and Eve. Their keys are $K_A=k_A(M,X^n)$ and $K_B=k_B(Y^n,\Phi)$. All design maps are fixed publicly before observations. Message and public alphabets follow the fixed-rate ceiling convention; the key alphabet at rate $R$ has exactly $2^{\lceil nR\rceil}$ labels. A weakly achievable rate $R$ has one sequence of such codes with disagreement tending to zero, $I(K_A;Z^n,\Phi)/n\to0$, and $\liminf H(K_A)/n\ge R$.
--
--   There is no excitation cost constraint. Rates and target exponents are nonnegative. Let $\mathcal R$ be the closure of triples $(R,E,F)$ attained by a single code sequence satisfying the entropy-rate lower bound and $\liminf[-\log_2\Pr(K_A\ne K_B)]/n\ge E$, $\liminf[-\log_2 I(K_A;Z^n,\Phi)]/n\ge F$. A zero error or leakage has decay rate $+\infty$. Strong achievability requires both $E>0$ and $F>0$.
--
--   For a channel stochastically degraded in Bob's favor, every normalized input law $p$ and rate
--   $$0\le R<I(X,S;Y)-I(X,S;Z)$$
--   yield a strongly achievable key rate. Zero rate is strongly achievable by the one-value-key protocol, and
--   $$\sup\{R:R\text{ strongly achievable}\}=C_{\rm SK}(\text{no cost constraint}).$$
--
--   This states strict-interior achievability and equality of suprema; it does not assert positive exponents at the maximizing endpoint.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 7, §IV-D, unnumbered strong achievability below degraded capacity (33)

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

/-- PDF pp.7--8, (33): strict interior rates are strong, and suprema agree.
No positive-exponent senderExcitedCapacity-endpoint claim. Zero rate uses one key value. -/
theorem strong_degraded (W : DMBC S X Y Z) (hdeg : SenderExcitedDegraded W) :
    (∀ p : S → ℝ, IsLaw p → ∀ R : ℝ, 0 ≤ R → R < advantage W p →
      StrongAchievable W R) ∧ StrongAchievable W 0 ∧
    strongCapacity W = senderExcitedCapacity W (fun _ => 0) none := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
