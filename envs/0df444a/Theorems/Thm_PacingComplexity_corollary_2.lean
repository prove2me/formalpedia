-- Prove2me | Theorems.Thm_PacingComplexity_corollary_2
-- name    : PacingComplexity.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:01.40754+00:00
-- url     : https://prove2.me/theorems/9cab1f0b-c957-4b3c-aba2-8700b0b48492
-- title:
--   Corollary 2: the expenditure of $C(p,s)$ on $N(p,s)_s$ (corrected: $n\ge3$)
-- statement:
--   Let $(A,B)$ be an $n\times n$ cost bimatrix game with all entries in $\{0,1\}$, let $G$ be the gadget SPP game built from it (with $\nu=1/(16n)$), and let $\delta=\gamma=1/n^7$. Let $(\alpha,x)$ be any $(\delta,\gamma)$-approximate pacing equilibrium of $G$, and write $\alpha(\cdot)$ for its pacing multipliers.
--   Assume $n\ge3$. Then for every $p\in\{1,2\}$ and $s\in[n]$, the expenditure $x_{C(p,s),N(p,s)_s}\,p_{N(p,s)_s}(\alpha)$ of buyer $C(p,s)$ on the normalization good $N(p,s)_s$ satisfies
--   $$
--   (1-\delta)\,\alpha(C(p,s))-\nu\ \le\ x_{C(p,s),N(p,s)_s}\,p_{N(p,s)_s}(\alpha)\ \le\ \alpha(C(p,s))-(1-\delta)\,\nu .
--   $$
--   So, up to $O(\nu)$, buyer $C(p,s)$ spends exactly $\alpha(C(p,s))$ on this good; Lemma 15 compares such spending across strategies.
--
--   Differences from the source:
--   - correction: every bimatrix dimension n → n ≥ 3; reason: false at n = 2: A = B = 0, δ = γ = 1/128, α(T) = 127/128, α(C(p,1)) = α(D(p,1)) = 1, α(C(p,2)) = α(D(p,2)) = 493/1000, C(p,1) taking all of N(p,1)_1 at price 1, the dummy buying fraction ν/α of N(p,2)_2 and every other good going to its top bidder, is an approximate PE in which C(1,1) spends 1 > α(C(1,1)) − (1 − δ)ν = 3969/4096 on N(1,1)_1 (exact check, corollary2_n2.py); the printed proof uses Lemma 13's bound 7/8, which needs n ≥ 3
--   - encoding: p ∈ {1, 2}, s ∈ [n], named buyers and goods → a two-element index (first = player 1), Fin n, inductive buyer and good types; δ = γ = 1/n⁷ and ν = 1/(16n) written out; A, B real with entries in {0, 1}; reason: Lean convention; same instances
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Corollary 2, p.32

import Mathlib
import Definitions.Def_PacingComplexity_IsApproxPE
import Definitions.Def_PacingComplexity_GBuyer
import Definitions.Def_PacingComplexity_GGood
import Definitions.Def_PacingComplexity_gadgetValue
import Definitions.Def_PacingComplexity_gadgetBudget
import Definitions.Def_PacingComplexity_secondBid

namespace PacingComplexity

/-- **Corollary 2** (Chen, Kroer, Kumar, *The Complexity of Pacing for Second-Price Auctions*,
arXiv:2103.13969v2, Appendix A, p.32): "For each p ∈ {1, 2} and s ∈ [n], the expenditure of
C(p, s) on N(p, s)s lies in the following interval [(1 − δ)α(C(p, s)) − ν, α(C(p, s)) − (1 − δ)ν]".

Let `(A, B)` be an `n × n` cost bimatrix game with entries in `{0, 1}`, `n ≥ 3`, `G` the gadget
game, `δ = γ = 1/n^7` and `ν = 1/(16n)`. In every `(δ, γ)`-approximate pacing equilibrium
`(α, x)` of `G`, the expenditure `x_{C(p,s), N(p,s)_s} · p_{N(p,s)_s}(α)` of `C(p, s)` on
`N(p, s)_s` lies in `[(1 − δ)α(C(p, s)) − ν, α(C(p, s)) − (1 − δ)ν]`.

**Formalization Note** Corrected to `n ≥ 3`, as for Lemma 13, whose bound `α(C(p, s)) ≤ 7/8`
the proof uses. At `n = 2` the corollary is false: with `A = B = 0`, `α(T) = 127/128`,
`α(C(p, 1)) = α(D(p, 1)) = 1` and `α(C(p, 2)) = α(D(p, 2)) = 493/1000` there is an approximate
pacing equilibrium in which `C(p, 1)` buys all of `N(p, 1)_1` at price `1`, above
`α(C(p, 1)) − (1 − δ)ν = 3969/4096`. Player `1` is `p = 0`, player `2` is `p = 1`. -/
theorem corollary_2 (n : ℕ) (hn : 3 ≤ n) (A B : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (hB : ∀ i j, B i j = 0 ∨ B i j = 1)
    (α : GBuyer n → ℝ) (x : GBuyer n → GGood n → ℝ)
    (hPE : IsApproxPE (gadgetValue n A B) (gadgetBudget n A B)
      (1 / (n : ℝ) ^ 7) (1 / (n : ℝ) ^ 7) α x)
    (p : Fin 2) (s : Fin n) :
    (1 - 1 / (n : ℝ) ^ 7) * α (.C p s) - 1 / (16 * (n : ℝ)) ≤
        x (.C p s) (.N p s s) * secondBid (gadgetValue n A B) α (.N p s s) ∧
      x (.C p s) (.N p s s) * secondBid (gadgetValue n A B) α (.N p s s) ≤
        α (.C p s) - (1 - 1 / (n : ℝ) ^ 7) * (1 / (16 * (n : ℝ))) := by sorry

end PacingComplexity
