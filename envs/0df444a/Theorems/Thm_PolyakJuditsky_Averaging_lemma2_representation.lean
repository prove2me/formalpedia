-- Prove2me | Theorems.Thm_PolyakJuditsky_Averaging_lemma2_representation
-- name    : PolyakJuditsky.Averaging.lemma2_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:39:18.652206+00:00
-- url     : https://prove2.me/theorems/c185a9bb-0edd-4393-a864-8f6f45dc93bb
-- title:
--   Lemma 2 — representation (A9) of $\sqrt t\,\bar\Delta_t$ for the linear recursion
-- statement:
--   Let $A$, $(\gamma_t)_{t\ge0}$ satisfy the hypotheses of Lemma 1, let $\Delta_0\in\mathbb R^N$, and let $\xi_1,\xi_2,\dots\in\mathbb R^N$ be an arbitrary sequence. Define
--   $$\Delta_t=\Delta_{t-1}-\gamma_t(A\Delta_{t-1}+\xi_t)\ (t\ge1),\qquad\bar\Delta_t=\frac1t\sum_{i=0}^{t-1}\Delta_i,\tag{A8}$$
--   and, with $X_j^t$ as in (A1), $\alpha_j^t=\gamma_j\sum_{i=j}^{t-1}X_{j+1}^{i+1}$, $\alpha_t=\alpha_0^t$, $w_j^t=\alpha_j^t-A^{-1}$. Then for every $t\ge1$
--   $$\sqrt t\,\bar\Delta_t=\frac1{\sqrt t\,\gamma_0}\,\alpha_t\Delta_0-\frac1{\sqrt t}\sum_{j=1}^{t-1}A^{-1}\xi_j-\frac1{\sqrt t}\sum_{j=1}^{t-1}w_j^t\xi_j,\tag{A9}$$
--   and there is $K<\infty$ with $\|\alpha_t\|\le K$ for all $t$, $\|w_j^t\|\le K$ for $1\le j<t$, and $\frac1t\sum_{j=1}^{t-1}\|w_j^t\|\to0$.
--
--   The identity is pathwise: no probability is involved. It isolates the leading term $-t^{-1/2}\sum_jA^{-1}\xi_j$, to which a martingale central limit theorem applies, from remainders that the bounds on $\alpha_t$, $w_j^t$ make negligible.
--
--   **Formalization Note** The paper prints (A9) with $+$ on both noise sums. For the recursion (A8) as printed ($-\gamma_t\xi_t$) the signs are $-$: at $t=2$, (A8) gives $\sqrt2\bar\Delta_2=\bigl((2I-\gamma_1A)\Delta_0-\gamma_1\xi_1\bigr)/\sqrt2$, while $A^{-1}+w_1^2=\alpha_1^2=\gamma_1I$. The first display of the proof (p. 847) drops the minus sign of (A8). The sign does not affect the bounds on $\alpha_t$, $w_j^t$. The matrices $\alpha_t$ and $w_j^t$ are the ones the proof constructs (p. 847), not arbitrary matrices with the stated bounds.
-- source:
--   Polyak, Juditsky, Acceleration of stochastic approximation by averaging, SIAM J. Control Optim. 30 (1992), p. 846, Lemma 2, Eq. (A8), (A9); p. 847, proof of Lemma 2

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open Filter Topology

namespace PolyakJuditsky.Averaging

/-- Lemma 2 (p. 846), sign-corrected. For the linear recursion (A8)
`Δ_t = Δ_{t-1} - γ_t (A Δ_{t-1} + ξ_t)` driven by an arbitrary sequence `ξ_1, ξ_2, … ∈ ℝ^N`
from an arbitrary `Δ_0`, with `Δ̄_t = (1/t) ∑_{i=0}^{t-1} Δ_i`, `α_t = α_0^t` and
`w_j^t = α_j^t - A⁻¹`: for every `t ≥ 1`,
`√t Δ̄_t = (1/(√t γ_0)) α_t Δ_0 - (1/√t) ∑_{j=1}^{t-1} A⁻¹ ξ_j - (1/√t) ∑_{j=1}^{t-1} w_j^t ξ_j`;
and under the hypotheses of Lemma 1 there is `K` with `‖α_t‖ ≤ K`, `‖w_j^t‖ ≤ K` for
`1 ≤ j < t`, and `(1/t) ∑_{j=1}^{t-1} ‖w_j^t‖ → 0`. -/
theorem lemma2_representation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ)
    (hA : EigenRePos A) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ)
    (Δ₀ : EuclideanSpace ℝ (Fin N)) (ξ : ℕ → EuclideanSpace ℝ (Fin N)) :
    (∀ t : ℕ, 1 ≤ t →
      Real.sqrt t • detAverage Δ₀ γ (matApply A) ξ t =
        (Real.sqrt t * γ 0)⁻¹ • matApply (lemAlpha A γ 0 t) Δ₀
          - (Real.sqrt t)⁻¹ • ∑ j ∈ Finset.Ico 1 t, matApply A⁻¹ (ξ j)
          - (Real.sqrt t)⁻¹ • ∑ j ∈ Finset.Ico 1 t, matApply (lemW A γ j t) (ξ j)) ∧
    ∃ K : ℝ, (∀ t, matNorm (lemAlpha A γ 0 t) ≤ K) ∧
      (∀ j t, 1 ≤ j → j < t → matNorm (lemW A γ j t) ≤ K) ∧
      Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * ∑ j ∈ Finset.Ico 1 t, matNorm (lemW A γ j t))
        atTop (𝓝 0) := by sorry

end PolyakJuditsky.Averaging
