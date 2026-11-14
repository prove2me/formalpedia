-- Prove2me | Theorems.Thm_WildeQIT_Feedback_eq_21_123
-- name    : WildeQIT.Feedback.eq_21_123
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T18:37:21.33224+00:00
-- url     : https://prove2.me/theorems/10b4cc9f-9a03-443d-9c2b-a76f7aa20971
-- title:
--   Eq. (21.116)–(21.123): $\log|\mathcal M|\le n\,I(p_{Y|X})+1+\varepsilon\log|\mathcal M|$ for every feedback code
-- statement:
--   Let $p_{Y|X}$ be a classical channel on finite alphabets $\mathcal X,\mathcal Y$, and let $I(p_{Y|X})=\max_{XX'}I(X;Y)$ be its mutual information (21.113). Consider any classical feedback code of block length $n$ with message set $\mathcal M$, $|\mathcal M|\ge1$: inputs $x_i(m,y^{i-1})$ depending on the message and the earlier outputs, and a decoder $g:\mathcal Y^n\to\mathcal M$. Let the message $M$ be uniformly distributed, let $M'=g(Y^n)$, and suppose $\Pr\{M'\neq M\}\le\varepsilon$ (21.115). Then
--
--   $$
--   \log|\mathcal M|\le n\,I(p_{Y|X})+1+\varepsilon\log|\mathcal M| .
--   $$
--
--   For $n\ge1$, writing $\frac1n\log|\mathcal M|=C-\delta$ and dividing by $n$, this is the book's final bound
--
--   $$
--   C-\delta\le I(p_{Y|X})+\frac1n+\frac{\varepsilon}{n}\log|\mathcal M|, \tag{21.123}
--   $$
--
--   the conclusion of the chain (21.116)–(21.122). It is the converse half of Theorem 21.5.1: letting $n\to\infty$ and $\varepsilon,\delta\to0$ gives $C\le I(p_{Y|X})$ for every rate achievable with feedback.
--
--   **Formalization Note** The feedback code, its output law $\prod_i p_{Y|X}(y_i|x_i(m,y^{i-1}))$ and its average error probability are `FeedbackCode`, `FeedbackCode.outputProb` and `FeedbackCode.errorProb`; $I(p_{Y|X})$ is the published `channelMaxMutualInfo N`, in bits. The bound is stated before division by $n$.
--
--   Differences from the source:
--   - reading: (n, C − δ, ε) feedback code with Pr{M′ ≠ M} ≤ ε (21.115) and "we assume that the message M is uniformly distributed" (p. 605) → FeedbackCode.errorProb N ≤ ε, the average error over a uniform message; reason: the page fixes the uniform message in the proof; the error criterion is then the average error
--   - encoding: C − δ ≤ I(pY|X) + 1/n + (ε/n) log|M| with (1/n) log|M| = C − δ → log|M| ≤ n·I(pY|X) + 1 + ε log|M| for every feedback code with |M| ≥ 1 messages; reason: multiply by n; for n ≥ 1 the two forms are equivalent, and naming C − δ := (1/n) log|M| covers every code
--   - generalization: block length n ≥ 1 (the bound divides by n) → every n, including n = 0; reason: the multiplied form also holds at n = 0 (Fano with a trivial output); at n ≥ 1 it is the book's (21.123)
--   - encoding: log|M| for a message set M → hypothesis 0 < M; reason: a message set with a uniform distribution is nonempty
--   - encoding: I(pY|X) = max_{XX′} I(X;Y) (21.113) → channelMaxMutualInfo N, the sSup of mutualInfo (N.joint p) over input distributions p; reason: with p_{XX′}(x,x′) = p_X(x)δ_{x,x′}, I(X;Y) = I(X′;Y) is the mutual information of p_X(x) p_{Y|X}(y|x); the set is bounded (by log|𝒴|), so the sSup is the supremum
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 21.5.1, eqs. (21.115)–(21.123), pp. 604–605

import Definitions.Def_WildeQIT_channelCode
import Definitions.Def_WildeQIT_Feedback_FeedbackCode_errorProb

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, proof of Theorem 21.5.1,
eqs. (21.116)–(21.123), pp. 604–605.
-/

namespace WildeQIT.Feedback

/-- **Converse bound for feedback codes, (21.116)–(21.123)** (Wilde, arXiv:1106.1445v8,
pp. 604–605). For every classical feedback code of block length `n` with `|𝓜| ≥ 1` messages
whose error probability `Pr{M′ ≠ M}` under a uniform message is at most `ε` (21.115),
`log |𝓜| ≤ n I(p_{Y|X}) + 1 + ε log |𝓜|`.

This is the chain (21.116)–(21.122),
`log |𝓜| ≤ I(M; M′) + 1 + ε log |𝓜| ≤ I(M; Yⁿ) + 1 + ε log |𝓜|` and
`I(M; Yⁿ) ≤ n max_{XX′} I(X; Y)`; dividing by `n` with `log |𝓜| = n(C − δ)` gives (21.123),
`C − δ ≤ I(p_{Y|X}) + 1/n + (ε/n) log |𝓜|`.

**Formalization Note.** The channel is the published `WildeQIT.Channel α β` on finite
alphabets; the feedback code, its output law `∏ᵢ N(yᵢ | xᵢ(m, y^{i−1}))` and its average error
probability are `FeedbackCode`, `FeedbackCode.outputProb`, `FeedbackCode.errorProb`.
`I(p_{Y|X}) = max_{XX′} I(X;Y)` (21.113) is the published `channelMaxMutualInfo N`, in bits.
The bound is stated in the form before division by `n`, which also covers `n = 0`. -/
theorem eq_21_123 {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (N : Channel α β) {n M : ℕ} (c : FeedbackCode α β n M) (hM : 0 < M) (ε : ℝ)
    (hε : c.errorProb N ≤ ε) :
    Real.logb 2 M ≤ n * channelMaxMutualInfo N + 1 + ε * Real.logb 2 M := by sorry

end WildeQIT.Feedback
