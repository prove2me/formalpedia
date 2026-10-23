-- Prove2me | Theorems.Thm_RandomGames_BRD_lemma_4_4
-- name    : RandomGames.BRD.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:58.153978+00:00
-- url     : https://prove2.me/theorems/31153a66-90a6-4701-82ca-55877998b31d
-- title:
--   Lemma 4.4, p. 15 — summably in N, every Hamming ball of radius ⌈δN⌉ has at most m_β vertices not accessible from 0
-- statement:
--   Let $\Xi_N$ be the random game with payoff law $\mu$ and suppose $\beta=\mathsf P(Z_1<Z_2)\in(0,1/2]$. For $r\in\mathbb N$ and a profile $\boldsymbol s$ let $B_r(\boldsymbol s)=\{\boldsymbol t : h(\boldsymbol s,\boldsymbol t)\le r\}$ be the Hamming ball (4.15), and let $m_\beta=\lfloor 1/(-\log_2(1-\beta))\rfloor$ (4.16). Then there is $\bar\delta>0$ such that for every $\delta<\bar\delta$,
--   $$\sum_{N=1}^\infty \mathsf P\Bigl(\exists\,\boldsymbol t:\ \mathsf{card}\bigl(B_{\lceil\delta N\rceil}(\boldsymbol t)\setminus\vec{\mathscr L}^{\beta,\mathbf 0}_N\bigr) > m_\beta\Bigr) < \infty. \tag{4.17}$$
--
--   So, for all large $N$, the profiles that best-response dynamics cannot reach from $\mathbf 0$ are sparse at every location: no ball of radius $\lceil\delta N\rceil$ contains more than $m_\beta$ of them. This is the input that excludes traps in the proof of Theorem 3.4.
--
--   **Formalization Note** $\vec{\mathscr L}^{\beta,\mathbf 0}_N$ is the set of profiles accessible from $\mathbf 0$ in the game. The hypothesis $\beta>0$ is $\alpha<1$; $\beta\le1/2$ holds for every law. For $\delta\le 0$ the radius `Nat.ceil (δ * N)` is $0$ and the ball is $\{\boldsymbol t\}$; the literal quantifier "for any $\delta<\bar\delta$" is kept.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 15, Lemma 4.4, (4.15)–(4.17)

import Mathlib
import Definitions.Def_RandomGames_BRD_Percolation

namespace RandomGames.BRD

open MeasureTheory

/-- Lemma 4.4, p. 15 (McDiarmid et al. 2020, Theorem 2(a)): for `β = P(Z₁ < Z₂) ∈ (0, 1/2]`
there is `δ̄ > 0` such that for every `δ < δ̄`, (4.17):
`∑_N P(∃ t, card(B_{⌈δN⌉}(t) \ L→^{β,0}_N) > m_β) < ∞`. -/
theorem lemma_4_4 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hβ : 0 < beta μ) :
    ∃ δbar : ℝ, 0 < δbar ∧ ∀ δ : ℝ, δ < δbar →
      ∑' N, gameMeasure μ N {Z | ∃ t : Profile N,
        mBeta (beta μ) < (((ball t (Nat.ceil (δ * N)) : Set (Profile N)) \ reach0 Z).ncard : ℤ)}
        ≠ ⊤ := by sorry

end RandomGames.BRD
