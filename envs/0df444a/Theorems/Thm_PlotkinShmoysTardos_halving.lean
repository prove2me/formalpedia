-- Prove2me | Theorems.Thm_PlotkinShmoysTardos_halving
-- name    : PlotkinShmoysTardos.halving
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:55:23.613726+00:00
-- url     : https://prove2.me/theorems/2377b57d-48ca-404f-b0ff-7c300ccde38e
-- title:
--   §4 p. 27 — a call that does not stop at G2 halves $\lambda$
-- statement:
--   Consider any call IMPROVE-GENERAL$(x)$, with input value $\lambda_0=\lambda(x)$. If the call returns other than because G2 holds, that is, because its loop test found $\lambda<\lambda_0/2$, then its output $x_{\mathrm{out}}$ satisfies
--   $$
--   \lambda(x_{\mathrm{out}})<\frac{\lambda_0}{2}.
--   $$
--   So between two calls of the driver that do not stop, the value $\lambda$ decreases by at least a factor of 2, which is what makes the total count of Theorem 4.5 a geometric sum.
--
--   Differences from the source:
--   - reading: the output (x, λ) does not satisfy G2 → the call returned through the λ < λ₀/2 exit (tag halved), not through its G2 test; reason: the call's exit reason is what the driver tests; a fresh G2 test of the output is not part of the algorithm
--   - generalization: a call within the algorithm (instance assumptions, λ₀ > 0) → any input x, ρ and map O, with no hypotheses; reason: the claim is a property of the exit test and holds for every input, so it specializes to the paper's calls
--   - reading: Figure 4 loop test 'x and y do not satisfy G2', then 'find a minimum-cost point x̃' → y is the dual of the current x for the call's fixed α, C_G(y) is the cost yᵗ(Ax̃ − b) of the oracle point x̃ = O(y), and the body reuses that x̃: one oracle call per evaluation of the test; reason: the figure computes y inside the body; the dual of the current x is the only y defined at the test, and x̃ attains C_G(y)
--   - encoding: rows i = 1, …, m → m ≥ 1 ([NeZero m]); reason: maxᵢ over no rows is undefined in the paper; excludes only that undefined case
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), §4, p. 27 ("Note that if the output (x, λ) of any call to IMPROVE-GENERAL does not satisfy G2, then the value λ must have decreased by at least a factor of 2.")

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality
import Definitions.Def_PlotkinShmoysTardos_improveGeneral

namespace PlotkinShmoysTardos

/-- **A call that does not stop at G2 halves `λ`.** Plotkin–Shmoys–Tardos, TR 999 (1992), §4,
p. 27: "Note that if the output `(x, λ)` of any call to IMPROVE-GENERAL does not satisfy G2, then
the value `λ` must have decreased by at least a factor of 2."
If the call IMPROVE-GENERAL(x) has returned other than through (G2) (tag `halved`), its output
`x_k` has `λ(x_k) < λ₀/2`, where `λ₀ = maxᵢ (aᵢ x − bᵢ)/dᵢ` is the call's input value. -/
theorem halving {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (ρ : ℝ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (k : ℕ)
    (hk : (callRun A b d ρ O x k).tag = Tag.halved) :
    lam A b d (callRun A b d ρ O x k).x < lam A b d x / 2 := by sorry

end PlotkinShmoysTardos
