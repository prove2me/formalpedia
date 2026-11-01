-- Prove2me | Theorems.Thm_PacingComplexity_lemma_15
-- name    : PacingComplexity.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:04.78962+00:00
-- url     : https://prove2.me/theorems/279faa23-e684-49e1-adbb-20783ca3b21f
-- title:
--   Lemma 15: $(x,y)$ is an $\varepsilon$-well-supported Nash equilibrium of $(A,B)$ (corrected: $n\ge129$)
-- statement:
--   Let $(A,B)$ be an $n\times n$ cost bimatrix game with all entries in $\{0,1\}$, let $G$ be the gadget SPP game built from it (with $\nu=1/(16n)$), and let $\delta=\gamma=1/n^7$. Let $(\alpha,x)$ be any $(\delta,\gamma)$-approximate pacing equilibrium of $G$, and write $\alpha(\cdot)$ for its pacing multipliers.
--   Assume $n\ge129$ and let $\varepsilon=1/n$ (so $\delta=\gamma=\varepsilon/n^6$). Let $x_s=x'_s/\sum_ix'_i$ and $y_s=y'_s/\sum_iy'_i$ be the strategies read off $\alpha$. Then $(x,y)\in\Delta_n\times\Delta_n$ is an $\varepsilon$-well-supported Nash equilibrium of the cost bimatrix game $(A,B)$:
--
--   1. $x_s>0$ implies $\sum_t A_{st}y_t\le\sum_t A_{kt}y_t+\varepsilon$ for every $k$;
--   2. $y_t>0$ implies $\sum_s x_sB_{st}\le\sum_s x_sB_{sk}+\varepsilon$ for every $k$.
--
--   This is the correctness of the reduction: every approximate pacing equilibrium of the gadget yields an answer to the bimatrix problem.
--
--   Differences from the source:
--   - correction: every bimatrix dimension n → n ≥ 129; reason: false at n = 3: with row 1 of A all ones and all other costs 0, there is an approximate PE of G (α(T) = 1, α(C(1,1)) ≈ 0.78594, α(C(1,2)) = α(C(1,3)) = 1/2, α(C(2,s)) ≈ 0.59632, each D equal to its C; exact check, counterexamples.py c3) whose x = e₁ and y uniform give row 1 cost 1 against row 2 cost 0, a gap 1 > ε = 1/3; the same family fails at n = 10 and n = 30; the printed proof drops the factor Σᵢ y′ᵢ (p.33), and with it restored it closes exactly from n = 129; 129 is the threshold of the proof, not a sharp one: 31 ≤ n ≤ 128 is neither refuted nor proved
--   - encoding: p ∈ {1, 2}, s ∈ [n], named buyers and goods → a two-element index (first = player 1), Fin n, inductive buyer and good types; δ = γ = 1/n⁷ and ν = 1/(16n) written out; A, B real with entries in {0, 1}; reason: Lean convention; same instances
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Lemma 15, p.33 (proof pp.33–34)

import Mathlib
import Definitions.Def_PacingComplexity_IsApproxPE
import Definitions.Def_PacingComplexity_GBuyer
import Definitions.Def_PacingComplexity_GGood
import Definitions.Def_PacingComplexity_gadgetValue
import Definitions.Def_PacingComplexity_gadgetBudget
import Definitions.Def_PacingComplexity_IsWSNE
import Definitions.Def_PacingComplexity_stratNorm

namespace PacingComplexity

/-- **Lemma 15** (Chen, Kroer, Kumar, *The Complexity of Pacing for Second-Price Auctions*,
arXiv:2103.13969v2, Appendix A, p.33), corrected: "(x, y) is an ε-well-supported Nash
equilibrium of the bimatrix game (A, B)."

Let `(A, B)` be an `n × n` cost bimatrix game with entries in `{0, 1}`, `n ≥ 129`, `ε = 1/n`,
`G` the gadget game and `δ = γ = ε/n^6 = 1/n^7`. For every `(δ, γ)`-approximate pacing
equilibrium `(α, x)` of `G`, the normalized strategies `x_s = x′_s / Σ_i x′_i`,
`y_s = y′_s / Σ_i y′_i` (`stratNorm`) form an `ε`-well-supported Nash equilibrium of `(A, B)`:
both lie in `∆n`, and both players' support conditions hold.

**Formalization Note** Corrected to `n ≥ 129`: at `n = 3` (row 1 of `A` all ones, all other
costs `0`) there is an approximate pacing equilibrium of `G` whose `(x, y)` puts all of `x` on
row 1, with cost gap `1 > ε = 1/3`. The printed proof drops the factor `Σ_i y′_i` in the
display on p.33; with it restored, the proof closes exactly from `n = 129`. -/
theorem lemma_15 (n : ℕ) (hn : 129 ≤ n) (A B : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hB : ∀ i j, B i j = 0 ∨ B i j = 1)
    (α : GBuyer n → ℝ) (x : GBuyer n → GGood n → ℝ)
    (hPE : IsApproxPE (gadgetValue n A B) (gadgetBudget n A B)
      (1 / (n : ℝ) ^ 7) (1 / (n : ℝ) ^ 7) α x) :
    IsWSNE (1 / (n : ℝ)) A B (stratNorm α 0) (stratNorm α 1) := by sorry

end PacingComplexity
