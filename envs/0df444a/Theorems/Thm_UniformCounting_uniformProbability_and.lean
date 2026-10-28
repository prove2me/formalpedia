-- Prove2me | Theorems.Thm_UniformCounting_uniformProbability_and
-- name    : UniformCounting.uniformProbability_and
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T15:18:47.048207+00:00
-- url     : https://prove2.me/theorems/ce1a4b69-1292-4259-bda6-210d5da11165
-- title:
--   $\mathbb{P}(A) + \mathbb{P}(B) - 1 \le \mathbb{P}(A \cap B)$ for the uniform counting probability
-- statement:
--   Let $\Omega$ be a finite type with uniform counting probability $\mathbb{P}$. For any two events $P, Q$,
--
--   $$
--   \mathbb{P}(P) \;+\; \mathbb{P}(Q) \;-\; 1 \;\le\; \mathbb{P}(P \wedge Q).
--   $$
--
--   This is the union bound in its complement form, and it is the standard way two
--   high-probability guarantees are combined: if $\mathbb{P}(P) \ge 1 - \alpha$ and
--   $\mathbb{P}(Q) \ge 1 - \beta$, then $\mathbb{P}(P \wedge Q) \ge 1 - \alpha - \beta$. In the
--   analysis of a randomized algorithm one typically proves one such bound for the algorithm's
--   value and another for the offline optimum, and needs them to hold simultaneously before they
--   can be combined into a single guarantee.
--
--   The proof is the inclusion-exclusion identity
--   $\#(S \cup T) + \#(S \cap T) = \#S + \#T$ together with $\#(S \cup T) \le \#\Omega$, divided
--   through by $\#\Omega$.
--
--   **Formalization Note** No nonemptiness hypothesis is needed: when $\#\Omega = 0$ every term is
--   $0$ in Lean's convention and the claim reads $-1 \le 0$. Decidability of the events is supplied
--   classically, as in the platform's `uniformProbability`.
-- source:
--   The two-event step in the high-probability analysis of Feldman, Mehta, Mirrokni & Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, Proc. 50th IEEE FOCS (2009) 117-126, DOI 10.1109/FOCS.2009.72, proof of Theorem 4; stated here for the uniform counting probability on an arbitrary finite sample space.

import Mathlib
import Definitions.Def_OnlineStochMatching_SuggestedMatching_BallsInBins

namespace UniformCounting

/-- The two-event bound for the uniform counting probability on a finite sample space:
`P(A) + P(B) - 1 ≤ P(A ∧ B)`, the complement form of the union bound. -/
theorem uniformProbability_and {Ω : Type} [Fintype Ω] (P Q : Ω → Prop) :
    OnlineStochMatching.SuggestedMatching.uniformProbability P +
        OnlineStochMatching.SuggestedMatching.uniformProbability Q - 1 ≤
      OnlineStochMatching.SuggestedMatching.uniformProbability (fun ω => P ω ∧ Q ω) := by sorry

end UniformCounting
