-- Prove2me | Theorems.Thm_WildeQIT_Feedback_theorem_21_5_1
-- name    : WildeQIT.Feedback.theorem_21_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:37:45.614568+00:00
-- url     : https://prove2.me/theorems/5892eb40-185a-44e5-9116-29c24d6d3a09
-- title:
--   Theorem 21.5.1 (Feedback Does Not Increase Classical Capacity): $\sup\{C : C\text{ achievable with feedback}\}=I(p_{Y|X})$
-- statement:
--   Let $p_{Y|X}(y|x)$ be a classical channel from a finite nonempty input alphabet $\mathcal X$ to a finite output alphabet $\mathcal Y$, and let
--
--   $$
--   I(p_{Y|X})=\max_{XX'}I(X;Y), \tag{21.113}
--   $$
--
--   where $XX'$ are correlated random variables with $p_{X,X'}(x,x')=p_X(x)\delta_{x,x'}$ and $X'$ is the channel input, so that $I(p_{Y|X})$ is the maximum over input distributions $p_X$ of the mutual information of the joint law $p_X(x)\,p_{Y|X}(y|x)$.
--
--   An $(n,C-\delta,\varepsilon)$ **classical feedback code** sends a uniformly distributed message $M\in\mathcal M$, $\frac1n\log|\mathcal M|=C-\delta$, over $n$ uses of the channel; the $i$-th input $x_i(m,Y^{i-1})$ is a function of the message and of all earlier outputs $Y_1,\dots,Y_{i-1}$, fed back noiselessly by the receiver, and the receiver decodes $M'=g(Y^n)$ with $\Pr\{M'\neq M\}\le\varepsilon$ (21.115). A rate $C$ is **achievable with feedback** if such codes exist for all $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$.
--
--   **Theorem.** The feedback capacity of the channel equals its mutual information:
--
--   $$
--   \sup\{C : C\text{ is achievable for }p_{Y|X}\text{ with feedback}\}=I(p_{Y|X}). \tag{21.114}
--   $$
--
--   The statement has two parts:
--
--   1. $I(p_{Y|X})$ is the least upper bound of the set of rates achievable with feedback;
--   2. the maximum in (21.113) is attained by some input distribution.
--
--   Free noiseless feedback from receiver to sender does not raise the capacity of a memoryless classical channel above Shannon's single-letter formula; this is the classical counterpart of the statement that quantum feedback does not increase the entanglement-assisted capacity (Theorem 21.5.2).
--
--   **Formalization Note** The channel is the published `WildeQIT.Channel α β`; feedback codes, their output law and their error probability are `FeedbackCode`, `FeedbackCode.outputProb` and `FeedbackCode.errorProb`; achievability with feedback is `IsAchievableWithFeedback`; $I(p_{Y|X})$ is the published `channelMaxMutualInfo N`, in bits. The book's setting is finite alphabets throughout.
--
--   Differences from the source:
--   - reading: "C is achievable for pY|X with feedback" (not defined on the page) → IsAchievableWithFeedback: ∀ ε ∈ (0,1), δ > 0, ∃ N₀, ∀ n ≥ N₀, an (n, C − δ, ε) feedback code; reason: the page defines the (n, C − δ, ε) feedback code; the achievability quantifiers are those of §14.10, p. 454, used throughout the book
--   - reading: Pr{M′ ≠ M} ≤ ε (21.115), "we assume that the message M is uniformly distributed" (p. 605) → FeedbackCode.errorProb N ≤ ε, the average error over a uniform message; reason: the page fixes the uniform message; the criterion is the average error, not the maximal error of §14.10
--   - encoding: an (n, C − δ, ε) code, rate (1/n) log|M| = C − δ → a feedback code with M ≥ 2^{n(C−δ)} messages; reason: 2^{n(C−δ)} is rarely an integer; under the average error criterion a code with more messages yields one with any smaller number by keeping the messages of smallest error, so "rate at least C − δ" is the book's notion
--   - reading: I(pY|X) = max_{XX′} I(X;Y) (21.113) → channelMaxMutualInfo N (an sSup over input distributions of mutualInfo (N.joint p)) together with the clause ∃ p, mutualInfo (N.joint p) = channelMaxMutualInfo N; reason: with p_{XX′}(x,x′) = p_X(x)δ_{x,x′}, I(X;Y) = I(X′;Y); the book's max presupposes attainment, and stating it is the stronger reading
--   - encoding: sup{C : C achievable with feedback} = I(pY|X) → IsLUB {C | IsAchievableWithFeedback N C} (channelMaxMutualInfo N); reason: Lean's sSup of a set that is not bounded above is 0; IsLUB says I(pY|X) is the least upper bound, which is what the equality of a real supremum with I(pY|X) means
--   - encoding: input alphabet of a channel → [Nonempty α]; reason: an empty input alphabet carries no input distribution and no code, a degenerate case the book does not consider
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 21.5.1, eqs. (21.113)–(21.115), p. 604

import Definitions.Def_WildeQIT_channelCode
import Definitions.Def_WildeQIT_Feedback_IsAchievableWithFeedback

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 21.5.1, p. 604.
-/

namespace WildeQIT.Feedback

/-- **Theorem 21.5.1 (Feedback Does Not Increase Classical Capacity)** (Wilde,
arXiv:1106.1445v8, p. 604, eq. (21.114)). The feedback capacity of a classical channel
`p_{Y|X}(y|x)` is equal to the mutual information of that channel:
`sup{C : C is achievable for p_{Y|X} with feedback} = I(p_{Y|X})`, where
`I(p_{Y|X}) = max_{XX′} I(X;Y)` (21.113).

The statement has two parts:
1. `I(p_{Y|X})` is the least upper bound of the set of rates achievable with feedback;
2. the maximum in (21.113) is attained: some input distribution `p_X` has
   `I(X;Y) = I(p_{Y|X})`.

**Formalization Note.** The channel is the published `WildeQIT.Channel α β` on finite
alphabets, the input alphabet nonempty. Achievability with feedback is
`IsAchievableWithFeedback`: for every `ε ∈ (0, 1)`, `δ > 0` and all sufficiently large `n` a
feedback code (each input `xᵢ(m, y^{i−1})` a function of the message and the earlier outputs)
with at least `2^{n(C−δ)}` messages and average error probability `Pr{M′ ≠ M} ≤ ε` for a
uniform message (21.115). `I(p_{Y|X})` is the published `channelMaxMutualInfo N`, the supremum
over input distributions `p_X` of `I(X;Y)` for the joint law `p_X(x) N(y|x)`, in bits; with
`p_{XX′}(x,x′) = p_X(x) δ_{x,x′}` this is (21.113). Part 1 is stated with `IsLUB` rather than
with `sSup`, because Lean's `sSup` of a set that is not bounded above is `0`. -/
theorem theorem_21_5_1 {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) :
    IsLUB {C : ℝ | IsAchievableWithFeedback N C} (channelMaxMutualInfo N) ∧
      ∃ p : FinDist α, mutualInfo (N.joint p) = channelMaxMutualInfo N := by sorry

end WildeQIT.Feedback
