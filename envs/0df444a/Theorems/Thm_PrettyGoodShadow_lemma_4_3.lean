-- Prove2me | Theorems.Thm_PrettyGoodShadow_lemma_4_3
-- name    : PrettyGoodShadow.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:55.69407+00:00
-- url     : https://prove2.me/theorems/29f0a3f8-2235-490c-9285-b2f2e8847c26
-- title:
--   Lemma 4.3, as printed — the bad mass of the prior is at most $2e^{-T/128}$ for $\|A\|_\infty\le1$, $k=\lceil12/\varepsilon^2\rceil$
-- statement:
--   Let $p$ be any prior and run Algorithm 1 with $k=\lceil12/\varepsilon^2\rceil$, for $\varepsilon>0$. Then, for every $T\ge1$ and every Hermitian observable $A$ with $\|A\|_\infty\le1$,
--
--   $$
--   \Pr_{x\sim p}\Big[\Pr_{\hat o\sim\mathcal A(x)}\big[|\hat o-\operatorname{tr}(A\rho_x)|>\varepsilon\big]>\tfrac18\Big]\le2e^{-T/128}.
--   $$
--
--   This is the literal form of the source's main technical lemma, in the setting of Problem 4.1.
--
--   **Formalization Note** The proof on pp.19–22 normalizes to $0\preceq O\preceq I$, replacing $\varepsilon$ by $\varepsilon/2$, and then uses $k\ge12/\varepsilon^2$ for that $\varepsilon$, so as written it gives this constant only for $0\preceq A\preceq I$, and $48/\varepsilon^2$ for $\|A\|_\infty\le1$. Those two forms are the item `lemma_4_3_normalized`, on which the goal rests. No counterexample to the literal form is known, and the goal does not depend on it.
--
--   Differences from the source:
--   - encoding: O_i, i ∈ [m], from a list with ∥O_i∥∞ ≤ 1 → one Hermitian matrix A with ∥A∥∞ ≤ 1; reason: the claim is for each i separately, and each O_i is an arbitrary such observable
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Lemma 4.3, p.18

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_PrettyGoodShadow_alg1Law

open scoped Matrix.Norms.L2Operator

namespace PrettyGoodShadow

/-- **Lemma 4.3, as printed** (arXiv:2610.06781, sha256 bd055b7d…, p.18). Let `p` be any prior and run Algorithm 1
with `k = ⌈12/ε²⌉`. Then, for every `T ≥ 1` and every observable `A` with `‖A‖_∞ ≤ 1` (Problem 4.1, p.17),
`Pr_{x∼p}[Pr_{ô∼A(x)}[|ô − tr(A ρ_x)| > ε] > 1/8] ≤ 2 e^{−T/128}`.

**Formalization Note** The literal form of the page. The proof on pp.19–22 normalizes to `0 ⪯ O ⪯ I`, replacing `ε` by
`ε/2`, and then uses `k ≥ 12/ε²` for that `ε`. It therefore gives this constant only for `0 ⪯ A ⪯ I`, and `48/ε²` for
`‖A‖_∞ ≤ 1`; those two forms are the item `lemma_4_3_normalized`, on which the goal rests. No counterexample to the
literal form is known, and the goal does not depend on it. The norm is the `L²` operator norm. -/
theorem lemma_4_3 {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (ρ : L → Matrix d d ℂ)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (p : L → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (A : Matrix d d ℂ) (hAh : A.IsHermitian) (hAn : ‖A‖ ≤ 1) (ε : ℝ)
    (hε : 0 < ε) (T : ℕ) (hT : 1 ≤ T) :
    ∑ x with 1 / 8 < errProb p ρ ⌈12 / ε ^ 2⌉₊ T A ε x, p x ≤
      2 * Real.exp (-(T : ℝ) / 128) := by sorry

end PrettyGoodShadow
