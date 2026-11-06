-- Prove2me | Theorems.Thm_PLIAG_condition_4_4
-- name    : PLIAG.condition_4_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:27:42.733539+00:00
-- url     : https://prove2.me/theorems/b1d26cfb-2456-4dda-8c62-2225bb67917d
-- title:
--   Proof of Theorem 4.2, p.26 — the step size (4.5) implies condition (4.4)
-- statement:
--   Let $\mu>0$, $L>0$, $\tau\in\mathbb N$, and let $\ell$ be monotonically increasing with $\ell(1)=1$. Let $0<\alpha\le\alpha_0$, with $\alpha_0$ given by (4.5), and set
--
--   $$
--   a:=\frac1{1+\alpha\mu},\qquad b:=\frac1\alpha,\qquad c:=L\,\ell(\tau+1),\qquad k_0:=\tau .
--   $$
--
--   Then condition (4.4) of Lemma 4.2 holds:
--
--   $$
--   \frac{c}{1-a}\cdot\frac{1-a^{k_0+1}}{a^{k_0}}\ \le\ b .
--   $$
--
--   This is the step of the proof of Theorem 4.2 that links the step-size rule (4.5) to Lemma 4.2.
--
--   Differences from the source:
--   - generalization: L = max_{k≥0} Σ_{j∈J_k} L_j → any real L > 0; reason: the paper’s L is positive (J_k ≠ ∅, L_j > 0), so the statement specializes to it
--   - encoding: ℓ monotonically increasing with ℓ(1) = 1 (introduced by B4 when τ > 0; ℓ(τ+1) = ℓ(1) = 1 when τ = 0) → ℓ : ℕ → ℝ with Monotone ℓ and ℓ 1 = 1 always; reason: when τ = 0 only ℓ(1) = 1 enters; ℓ(0) is never read and a monotone ℓ on the positive integers extends by ℓ(0) := ℓ(1)
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, proof of Theorem 4.2, p.26

import Mathlib
import Definitions.Def_PLIAG_alpha0

namespace PLIAG

/-- **(4.5) implies condition (4.4)** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, proof of
Theorem 4.2, p.26). With `a := 1/(1+αμ)`, `b := 1/α`, `c := Lℓ(τ+1)` and `k_0 := τ`, every step
`0 < α ≤ α_0` (4.5) satisfies `(c/(1−a)) · (1 − a^{k_0+1})/a^{k_0} ≤ b` (4.4).

**Formalization Note.** Stated for any real `L > 0` (in the paper `L = max_k Σ_{j∈J_k} L_j > 0`),
`μ > 0` (B3) and `ℓ` monotone with `ℓ(1) = 1` (B4). -/
theorem condition_4_4 (μ L : ℝ) (ℓ : ℕ → ℝ) (τ : ℕ) (α : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) (hα : 0 < α) (hαle : α ≤ alpha0 μ L ℓ τ) :
    L * ℓ (τ + 1) / (1 - 1 / (1 + α * μ)) *
        ((1 - (1 / (1 + α * μ)) ^ (τ + 1)) / (1 / (1 + α * μ)) ^ τ) ≤ 1 / α := by sorry

end PLIAG
