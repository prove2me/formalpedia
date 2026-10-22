-- Prove2me | Theorems.Thm_WalledBrauer_Blocks_lemma_8_1
-- name    : WalledBrauer.Blocks.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:20.384758+00:00
-- url     : https://prove2.me/theorems/0bbb0c61-2a5d-4447-b0a8-b1e438275e3f
-- title:
--   Lemma 8.1 (corrected: "for all $i$") — the counting form of $\delta$-balance
-- statement:
--   Let $\delta\in\mathbb Z$, and for a partition $\lambda$ let $c_i(\lambda)$ be the number of boxes of $\lambda$ of content $i$. Two bipartitions $(\mu^L,\mu^R)$ and $(\lambda^L,\lambda^R)$ are $\delta$-balanced if and only if
--   $$
--   c_i(\lambda^L)-c_i(\mu^L)=c_{-\delta-i}(\lambda^R)-c_{-\delta-i}(\mu^R)\qquad\text{for all } i\in\mathbb Z. \tag{24}
--   $$
--
--   The printed (24) omits "for all $i\in\mathbb Z$", which the proof uses; it is stated here with the quantifier. The counting form is what makes balance comparable with orbits of the dot action in Section 8.
--
--   **Formalization Note** The bipartitions are arbitrary pairs of Young diagrams (no size or row bound). Balance is taken in $\mathbb Z$.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 32, Lemma 8.1 (eq. (24))

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_Partitions

namespace WalledBrauer.Blocks

/-- Lemma 8.1 (p. 32), with the intended quantifier "for all `i ∈ ℤ`" (missing in the printed
(24)). Two bipartitions `(μL, μR)` and `(λL, λR)` are `δ`-balanced (`δ ∈ ℤ`) if and only if
`c_i(λL) - c_i(μL) = c_{-δ-i}(λR) - c_{-δ-i}(μR)` for every integer `i`, where `c_i(λ)` is the
number of boxes of `λ` of content `i`. -/
theorem lemma_8_1 (δ : ℤ) (lamL lamR muL muR : YoungDiagram) :
    IsBalanced δ lamL lamR muL muR ↔
      ∀ i : ℤ, (contentCount lamL i : ℤ) - contentCount muL i =
        (contentCount lamR (-δ - i) : ℤ) - contentCount muR (-δ - i) := by sorry

end WalledBrauer.Blocks
