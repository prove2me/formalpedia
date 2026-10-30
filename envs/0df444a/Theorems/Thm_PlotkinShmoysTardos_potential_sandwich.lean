-- Prove2me | Theorems.Thm_PlotkinShmoysTardos_potential_sandwich
-- name    : PlotkinShmoysTardos.potential_sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:54:16.909478+00:00
-- url     : https://prove2.me/theorems/6cec4450-e133-4c7d-9521-afaa7908879f
-- title:
--   §4 p. 27 — during one call $e^{\alpha\lambda_0/2}\le\Phi\le me^{\alpha\lambda_0}$
-- statement:
--   Consider an instance of the GENERAL problem ($m\ge1$, $d>0$, $P$ convex, $\rho$ a width bound) and a subroutine $O$ for (10). Run IMPROVE-GENERAL from $x\in P$ with $\lambda_0=\lambda(x)>0$ and $\alpha=4\lambda_0^{-1}\ln(6m\rho\lambda_0^{-1})$, and let $x_k$ be its iterate after $k$ steps and $\Phi(x_k)=\sum_i e^{\alpha(a_ix_k-b_i)/d_i}$. Then for every $k$:
--   1. $\Phi(x_k)\le m\,e^{\alpha\lambda_0}$;
--   2. if the loop is running at $x_k$, i.e. $\lambda(x_k)\ge\lambda_0/2$, then $e^{\alpha\lambda_0/2}\le\Phi(x_k)$.
--
--   Together with the decrease of Lemma 4.3 this bounds the number of iterations of one call (Theorem 4.4).
--
--   Differences from the source:
--   - reading: during a single call, e^{αλ₀/2} ≤ Φ ≤ me^{αλ₀} → the upper bound at every iterate of the call; the lower bound at every iterate with λ(x_k) ≥ λ₀/2; reason: the lower bound cannot hold at the exit point where λ < λ₀/2; 'during' is while the loop runs
--   - reading: Figure 4 loop test 'x and y do not satisfy G2', then 'find a minimum-cost point x̃' → y is the dual of the current x for the call's fixed α, C_G(y) is the cost yᵗ(Ax̃ − b) of the oracle point x̃ = O(y), and the body reuses that x̃: one oracle call per evaluation of the test; reason: the figure computes y inside the body; the dual of the current x is the only y defined at the test, and x̃ attains C_G(y)
--   - generalization: ρ = maxᵢ max_{x∈P} |aᵢx − bᵢ|/dᵢ, the exact width → any ρ with |aᵢx − bᵢ| ≤ ρdᵢ for all i and x ∈ P (IsWidthBound), used by the algorithm; reason: the exact width satisfies the bound, so the Lean statement specializes to the paper's; it also avoids assuming the max is attained
--   - encoding: α = 4λ₀⁻¹ln(6mρλ₀⁻¹) → 0 < λ₀; reason: α is undefined otherwise; the driver only calls with λ₀ > ε > 0
--   - encoding: rows i = 1, …, m → m ≥ 1 ([NeZero m]); reason: maxᵢ over no rows is undefined in the paper; excludes only that undefined case
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), §4, p. 27 ("Observe that during a single call to IMPROVE-GENERAL we have e^{αλ₀/2} ≤ Φ ≤ me^{αλ₀}.")

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_General
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality
import Definitions.Def_PlotkinShmoysTardos_improveGeneral

namespace PlotkinShmoysTardos

/-- **Potential bounds during one call.** Plotkin–Shmoys–Tardos, TR 999 (1992), §4, p. 27:
"Observe that during a single call to IMPROVE-GENERAL we have `e^{αλ₀/2} ≤ Φ ≤ me^{αλ₀}`."
For a call started at `x ∈ P` with `λ₀ = maxᵢ (aᵢ x − bᵢ)/dᵢ > 0` and `α = 4λ₀⁻¹ ln(6mρλ₀⁻¹)`
(`d > 0`, `P` convex, `ρ` a width bound, `O` a subroutine (10)), every iterate `x_k` of the call
has `Φ(x_k) ≤ m e^{αλ₀}`, and every iterate at which the loop runs (`λ(x_k) ≥ λ₀/2`) has
`e^{αλ₀/2} ≤ Φ(x_k)`. -/
theorem potential_sandwich {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (P : Set (Fin n → ℝ)) (hd : ∀ i, 0 < d i) (hP : Convex ℝ P) (ρ : ℝ)
    (hρ : IsWidthBound A b d P ρ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (hO : IsMinOracle A P O)
    (x : Fin n → ℝ) (hx : x ∈ P) (hl : 0 < lam A b d x) (k : ℕ) :
    potential A b d (alphaOf m ρ (lam A b d x)) (callRun A b d ρ O x k).x ≤
        (m : ℝ) * Real.exp (alphaOf m ρ (lam A b d x) * lam A b d x) ∧
      (lam A b d x / 2 ≤ lam A b d (callRun A b d ρ O x k).x →
        Real.exp (alphaOf m ρ (lam A b d x) * lam A b d x / 2) ≤
          potential A b d (alphaOf m ρ (lam A b d x)) (callRun A b d ρ O x k).x) := by sorry

end PlotkinShmoysTardos
