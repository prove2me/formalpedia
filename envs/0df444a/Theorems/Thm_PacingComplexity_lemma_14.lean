-- Prove2me | Theorems.Thm_PacingComplexity_lemma_14
-- name    : PacingComplexity.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:09.366833+00:00
-- url     : https://prove2.me/theorems/72fbc664-02da-4167-942e-ba993425898b
-- title:
--   Lemma 14: $\sum_s x'_s>1/8$ and $\sum_s y'_s>1/8$
-- statement:
--   Let $(A,B)$ be an $n\times n$ cost bimatrix game with all entries in $\{0,1\}$, let $G$ be the gadget SPP game built from it (with $\nu=1/(16n)$), and let $\delta=\gamma=1/n^7$. Let $(\alpha,x)$ be any $(\delta,\gamma)$-approximate pacing equilibrium of $G$, and write $\alpha(\cdot)$ for its pacing multipliers.
--   Assume $n\ge2$. With $x'_s=\{\alpha(C(1,s))-\alpha(T)/2\}^+$ and $y'_s=\{\alpha(C(2,s))-\alpha(T)/2\}^+$,
--   $$
--   \sum_{s\in[n]}x'_s>\frac18\qquad\text{and}\qquad\sum_{s\in[n]}y'_s>\frac18 .
--   $$
--   In particular the normalized strategies $x_s=x'_s/\sum_ix'_i$ and $y_s=y'_s/\sum_iy'_i$ are well defined probability distributions.
--
--   Differences from the source:
--   - encoding: every bimatrix dimension n (Definition 2 needs δ < 1) → n ≥ 2; reason: at n = 1, δ = 1/n⁷ = 1 lies outside Definition 2's range δ, γ ∈ [0, 1), so n ≥ 2 only excludes undefined cases
--   - encoding: p ∈ {1, 2}, s ∈ [n], named buyers and goods → a two-element index (first = player 1), Fin n, inductive buyer and good types; δ = γ = 1/n⁷ and ν = 1/(16n) written out; A, B real with entries in {0, 1}; reason: Lean convention; same instances
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Lemma 14, p.32

import Mathlib
import Definitions.Def_PacingComplexity_IsApproxPE
import Definitions.Def_PacingComplexity_GBuyer
import Definitions.Def_PacingComplexity_GGood
import Definitions.Def_PacingComplexity_gadgetValue
import Definitions.Def_PacingComplexity_gadgetBudget
import Definitions.Def_PacingComplexity_stratPrime

namespace PacingComplexity

/-- **Lemma 14** (Chen, Kroer, Kumar, *The Complexity of Pacing for Second-Price Auctions*,
arXiv:2103.13969v2, Appendix A, p.32): "The following inequalities hold: Σ_s x′_s > 1/8 and
Σ_s y′_s > 1/8."

Let `(A, B)` be an `n × n` cost bimatrix game with entries in `{0, 1}`, `n ≥ 2`, `G` the gadget
game and `δ = γ = 1/n^7`. In every `(δ, γ)`-approximate pacing equilibrium `(α, x)` of `G`,
with `x′_s = {α(C(1, s)) − α(T)/2}⁺` and `y′_s = {α(C(2, s)) − α(T)/2}⁺` (`stratPrime`), both
`Σ_s x′_s > 1/8` and `Σ_s y′_s > 1/8`.

**Formalization Note** `n ≥ 2` keeps `δ = 1/n^7 < 1` (Definition 2 takes `δ, γ ∈ [0, 1)`).
`stratPrime α 0` is `x′`, `stratPrime α 1` is `y′`. -/
theorem lemma_14 (n : ℕ) (hn : 2 ≤ n) (A B : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hB : ∀ i j, B i j = 0 ∨ B i j = 1)
    (α : GBuyer n → ℝ) (x : GBuyer n → GGood n → ℝ)
    (hPE : IsApproxPE (gadgetValue n A B) (gadgetBudget n A B)
      (1 / (n : ℝ) ^ 7) (1 / (n : ℝ) ^ 7) α x) :
    1 / 8 < ∑ s, stratPrime α 0 s ∧ 1 / 8 < ∑ s, stratPrime α 1 s := by sorry

end PacingComplexity
