-- Prove2me | Theorems.Thm_SuttonTD_Convergence_powers_tendsto_zero
-- name    : SuttonTD.Convergence.powers_tendsto_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:50.883987+00:00
-- url     : https://prove2.me/theorems/9fa16a21-bdcf-4720-9d45-b9ecdd8168b6
-- title:
--   Step-size threshold: $(I-\alpha X^\top X D(I-Q))^n\to0$ for $0<\alpha<\varepsilon$
-- statement:
--   Let $X$ be a real $K\times N$ matrix with linearly independent columns and let $M$ be an $N\times N$ real matrix that is positive definite in the paper's sense (the paper's $M=D(I-Q)$). Then there is $\varepsilon>0$ such that for every $\alpha$ with $0<\alpha<\varepsilon$,
--
--   $$\lim_{n\to\infty}\bigl(I-\alpha X^\top XM\bigr)^n=0 .$$
--
--   This is the remaining step of the proof of Theorem 2.
--
--   **Formalization Note** On p. 28 the paper writes $I-\alpha XD(I-Q)X^\top$ (twice); this is a slip for the $N\times N$ matrix $I-\alpha X^\top XD(I-Q)$ of p. 26, which is the one stated.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, pp. 26 and 28 (PDF pp. 18 and 20)

import Definitions.Def_SuttonTD_Convergence_IsPosDefReal
open Filter Topology Matrix

namespace SuttonTD.Convergence

/-- **The step-size threshold** (Sutton 1988, §4.1, pp. 26 and 28, PDF pp. 18 and 20): "It thus
remains to show that `lim_{n→∞} (I − αXᵀXD(I − Q))ⁿ = 0`." Stated for any `M` positive definite
in the paper's sense (the paper's `M = D(I − Q)`): if `X` has linearly independent columns, there
is `ε > 0` such that for every `α` with `0 < α < ε`, `(I − α XᵀX M)ⁿ → 0`.

Formalization Note: p. 28 prints the matrix as `I − αXD(I − Q)Xᵀ` (twice), a slip for the
`N × N` matrix `I − αXᵀXD(I − Q)` of p. 26; the latter is stated. -/
theorem powers_tendsto_zero {N : Type*} [Fintype N] [DecidableEq N] {K : ℕ}
    (X : Matrix (Fin K) N ℝ) (hX : LinearIndependent ℝ (fun i : N => fun k : Fin K => X k i))
    (M : Matrix N N ℝ) (hM : IsPosDefReal M) :
    ∃ ε > 0, ∀ α : ℝ, 0 < α → α < ε →
      Tendsto (fun n : ℕ => (1 - α • (Xᵀ * X * M)) ^ n) atTop (𝓝 0) := by sorry

end SuttonTD.Convergence
