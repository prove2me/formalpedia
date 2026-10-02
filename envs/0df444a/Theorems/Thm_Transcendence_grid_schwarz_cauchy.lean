-- Prove2me | Theorems.Thm_Transcendence_grid_schwarz_cauchy
-- name    : Transcendence.grid_schwarz_cauchy
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:36.38041+00:00
-- url     : https://prove2.me/theorems/8b855f06-5713-4fa8-9781-42d2ffa24c05
-- title:
--   Schwarz's lemma on the lattice grid {Σ s_j y_j}, then Cauchy's inequality: a bound for the derivatives of the first non-vanishing order
-- statement:
--   Let $\iota$ be a finite set with $n = |\iota| \ge 1$, and let $(y_j)_{j\in\iota}$ be a basis of $\mathbb{C}^\iota$. There is a constant $c \ge 1$ with the following property. Let $F$ be an entire function on $\mathbb{C}^\iota$, let $S_0$, $S_1 \ge 1$ and $M \ge nS_0$ be integers, and let $\rho \ge 1$ and $B$ be real numbers. Suppose that every derivative of $F$ of total order less than $M$ vanishes at every point $\sum_j s_jy_j$ with $0 \le s_j < S_1$, and that $|F| \le B$ on the closed polydisc of radius $cS_1\rho$ about $0$. Then at every such point, the derivative of $F$ along any list of $M$ coordinate directions has modulus at most
--
--   $$M!\cdot n\,\rho^{-S_0S_1}B.$$
--
--   It is step 5 of §4.6 of Waldschmidt's book, for any entire function: Schwarz's lemma for Cartesian products (`Transcendence.cartesian_schwarz`) is applied to $F\bigl(\sum_j z_jy_j\bigr)$ on the grid $\{0, \dots, S_1 - 1\}^n$, and Cauchy's inequality (`Transcendence.polydisc_cauchy`) on the unit polydisc about the grid point; $\rho$ plays the role of the book's $E'$.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: step 5 of §4.6 of the book (p. 140). The book applies Proposition 4.7 to $F\bigl(\sum_j z_jy_j\bigr)$ under a vanishing hypothesis (every exponent below $S_0'$) that this change of variables does not preserve; vanishing by total order, assumed here, is preserved. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, §4.6, step 5 (p. 140), with Proposition 4.7 (p. 122) and Cauchy's inequalities (p. XVII). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **Schwarz's lemma on a lattice grid, then Cauchy's inequality** (Waldschmidt, *Diophantine Approximation on
Linear Algebraic Groups*, Prop. 4.7, moved to the grid `{Σ_j s_j y_j : 0 ≤ s_j < S₁}` by `z ↦ Σ_j z_j y_j`). Let
`(y_j)` be a basis of `ℂ^ι`, `n = |ι| ≥ 1`. There is a constant `c ≥ 1` such that for every entire function `F`
on `ℂ^ι`: if every derivative of `F` of total order `< M` vanishes at every grid point, where `n S₀ ≤ M`, and
`|F| ≤ B` on the polydisc of radius `c S₁ ρ` (`S₁ ≥ 1`, `ρ ≥ 1`), then every mixed partial derivative of order
`M` of `F` at a grid point, along coordinate directions, is at most `M! · n ρ^{-S₀S₁} B`. -/
theorem grid_schwarz_cauchy {ι : Type*} [Fintype ι] [DecidableEq ι] (hn : 0 < Fintype.card ι)
    (y : ι → ι → ℂ) (hy : LinearIndependent ℂ y) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ F : (ι → ℂ) → ℂ, AnalyticOnNhd ℂ F Set.univ →
      ∀ (S₀ S₁ M : ℕ) (ρ B : ℝ), 1 ≤ S₁ → 1 ≤ ρ → Fintype.card ι * S₀ ≤ M →
      (∀ k < M, ∀ s : ι → Fin S₁, iteratedFDeriv ℂ k F (∑ j, ((s j : ℕ) : ℂ) • y j) = 0) →
      (∀ w : ι → ℂ, ‖w‖ ≤ c * S₁ * ρ → ‖F w‖ ≤ B) →
      ∀ (s : ι → Fin S₁) (L : Fin M → ι),
        ‖iteratedFDeriv ℂ M F (∑ j, ((s j : ℕ) : ℂ) • y j) (fun l => Pi.single (L l) 1)‖ ≤
          M.factorial * (Fintype.card ι * ρ⁻¹ ^ (S₀ * S₁) * B) := by
  sorry

end Transcendence
