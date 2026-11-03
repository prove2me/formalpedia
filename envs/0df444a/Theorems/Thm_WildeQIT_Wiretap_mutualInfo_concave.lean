-- Prove2me | Theorems.Thm_WildeQIT_Wiretap_mutualInfo_concave
-- name    : WildeQIT.Wiretap.mutualInfo_concave
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:10.777234+00:00
-- url     : https://prove2.me/theorems/132dd51b-5f53-430e-9734-bc090567387d
-- title:
--   Mutual information is concave in the input distribution
-- statement:
--   **Theorem 13.1.2.** Fix a classical channel $p_{Y|X}(y|x)$ with finite alphabets. Then the mutual information $I(X;Y)$ is concave in the input density $p_X$: for input densities $p_{X_1}$, $p_{X_2}$ and $\lambda\in[0,1]$,
--
--   $$
--   \lambda\, I(X_1;Y)+(1-\lambda)\, I(X_2;Y)\le I(Z;Y),
--   $$
--
--   where $X_1$ has density $p_{X_1}$, $X_2$ has density $p_{X_2}$, $Z$ has the mixture density $\lambda p_{X_1}(x)+(1-\lambda)p_{X_2}(x)$, and in each mutual information the output $Y$ is produced from the input by the fixed channel.
--
--   Concavity makes the maximization in the definition of $I(N)$ a convex optimization problem.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second).
--
--   Differences from the source:
--   - encoding: Z has density λ p_{X1}(x) + (1 − λ) p_{X2}(x) → a distribution q with q.prob x = λ p₁.prob x + (1 − λ) p₂.prob x for every x; reason: the hypothesis determines q uniquely, so the same instances
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.1.2, eq. (13.54), p. 395

import Definitions.Def_WiretapFeedback_jointLaw
import Definitions.Def_WildeQIT_mutualInfo

namespace WildeQIT.Wiretap

open WildeQIT

/-- **Theorem 13.1.2 (concavity of mutual information in the input density).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.1.2, (13.54),
p. 395: fix the conditional density `p_{Y|X}(y|x)`. Then `I(X; Y)` is concave in the marginal
density `p_X(x)`: `λ I(X₁; Y) + (1 − λ) I(X₂; Y) ≤ I(Z; Y)`, where `X₁` has density `p_{X₁}`,
`X₂` has density `p_{X₂}`, and `Z` has density `λ p_{X₁}(x) + (1 − λ) p_{X₂}(x)`, for `λ ∈ [0, 1]`.

Each mutual information is computed from the joint density `p(x) p_{Y|X}(y|x)` of the input and
the output of the fixed channel `N`; `q` is the mixture density of `Z`. -/
theorem mutualInfo_concave {α β : Type} [Fintype α] [Fintype β] (N : Channel α β)
    (p₁ p₂ q : FinDist α) (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (hq : ∀ x, q.prob x = lam * p₁.prob x + (1 - lam) * p₂.prob x) :
    lam * mutualInfo (WiretapFeedback.jointLaw p₁ N) + (1 - lam) * mutualInfo (WiretapFeedback.jointLaw p₂ N)
      ≤ mutualInfo (WiretapFeedback.jointLaw q N) := by sorry

end WildeQIT.Wiretap
