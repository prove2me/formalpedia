-- Prove2me | Theorems.Thm_RandomGames_BRD_lemma_4_3
-- name    : RandomGames.BRD.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:59.350186+00:00
-- url     : https://prove2.me/theorems/8f4ea89e-899b-4758-a0fc-dedc2cb3de00
-- title:
--   Lemma 4.3, p. 14 — the fragment of percolation on the hypercube concentrates around (2(1 − β))^N(1 + O(N(1 − β)^N)), summably in N
-- statement:
--   Fix $\beta\in(0,1/2)$ and let $\mathscr M^\beta_N$ be the fragment (the vertices outside the giant component) of bond percolation $\mathscr B^\beta_N$ on the hypercube. Then for every $\varepsilon>0$,
--   $$\sum_{N=1}^\infty \mathsf P\Bigl(\bigl|\mathsf{card}(\mathscr M^\beta_N)-\mathsf E[\mathsf{card}(\mathscr M^\beta_N)]\bigr| \ge \varepsilon\sqrt{N(2(1-\beta))^N}\Bigr) < \infty, \tag{4.10}$$
--   and
--   $$\mathsf E[\mathsf{card}(\mathscr M^\beta_N)] = (2(1-\beta))^N\bigl(1+O(N(1-\beta)^N)\bigr).$$
--
--   The lemma is McDiarmid, Scott and Withers (2020, Theorem 1(a)); the paper uses it to show that $\mathbf 0$ lies in the giant component (Proposition 4.2).
--
--   **Formalization Note** The $O(\cdot)$ clause is read two-sided: there is $C$ with $\bigl|\mathsf E[\mathsf{card}(\mathscr M^\beta_N)]-(2(1-\beta))^N\bigr| \le C\,(2(1-\beta))^N\,N(1-\beta)^N$ for all $N\ge1$ (the paper's definition on p. 14 bounds the ratio from above only; the two-sided form is stronger and true, since isolated vertices alone contribute $(2(1-\beta))^N$). The expectation is a Bochner integral of a bounded function on a finite probability space.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 14, Lemma 4.3, (4.10)

import Mathlib
import Definitions.Def_RandomGames_BRD_Percolation

namespace RandomGames.BRD

open MeasureTheory

/-- Lemma 4.3, p. 14 (McDiarmid et al. 2020, Theorem 1(a)): for fixed `β ∈ (0, 1/2)`, (4.10)
holds for every `ε > 0`, and `E[card(M^β_N)] = (2(1 − β))^N (1 + O(N(1 − β)^N))`. -/
theorem lemma_4_3 (β : ℝ) (hβ0 : 0 < β) (hβ : β < 1 / 2) :
    (∀ ε : ℝ, 0 < ε →
      ∑' N, percMeasure β N {ω | ε * Real.sqrt (N * (2 * (1 - β)) ^ N) ≤
        |(fragmentCard ω : ℝ) - ∫ ω', (fragmentCard ω' : ℝ) ∂(percMeasure β N)|} ≠ ⊤) ∧
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∫ ω, (fragmentCard ω : ℝ) ∂(percMeasure β N) - (2 * (1 - β)) ^ N| ≤
        C * (2 * (1 - β)) ^ N * (N * (1 - β) ^ N) := by sorry

end RandomGames.BRD
