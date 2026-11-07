-- Prove2me | Theorems.Thm_SetMultCost_proof_theorem_1_2_bound
-- name    : SetMultCost.proof_theorem_1_2_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:01.017293+00:00
-- url     : https://prove2.me/theorems/b1317991-0802-44ff-b0f6-e2cdfe919f7f
-- title:
--   Proof of Theorem 1.2, final display — the bound $s\ge d^{-O(d)}n^{\Omega(d^{1/R}/p^2)}$
-- statement:
--   For each $\Delta\ge1$ there are constants $K,c_1>0$ and $n_0$ such that the following holds for every field $F$ of prime characteristic $p$. Let $n\ge n_0$, $d\ge2$, and let $M$ be an integer with $M\ge200p^2$ and $\frac23M^{R(\Delta)}\le d\le M^{R(\Delta)}$, where $2d\le\log_2n$ and $d\le\sqrt n$. Every circuit of product-depth at most $\Delta$ computing $\mathrm{IMM}_{n,d}$, of size $s$, satisfies
--
--   $$s\ge d^{-Kd}\cdot n^{c_1d^{1/R(\Delta)}/p^2}.$$
--
--   Only the elementary bookkeeping with the range of $d$ remains between this and the main theorem.
--
--   Differences from the source:
--   - generalization: "the smallest set-multilinear product-depth ∆ circuit computing P" (p.25) → any circuit of product-depth at most Δ computing IMM_{n,d}; reason: the proof set-multilinearizes it, so it must be general, and the set-multilinear case is an instance
--   - reading: s ≥ d^{−O(d)} · n^{Ω(d^{1/F(∆+1)−1}/p²)} → explicit K, c₁, n₀ depending on Δ only, chosen before F and p; reason: the explicit p² only has content with constants uniform in p
--   - encoding: the ranges "d large enough", d = O(log n/log log n), "M ≥ 200c²" with c = p + 1 → M ≥ 200p², 2d ≤ log₂ n, d ≤ √n; reason: Theorem 3.5 gives fan-in p, and these are the ranges the proof uses (Corollary 2.7, Lemma 7.3)
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Proof of Theorem 1.2, p.25

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SetMultCost_Circuit_HasProductDepthLE
import Definitions.Def_SetMultCost_imm
import Definitions.Def_SetMultCost_fibF

universe u

namespace SetMultCost

/-- **Proof of Theorem 1.2, final display.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.25: "s ≥ d^{−O(d)} · n^{Ω(d^{1/F(∆+1)−1}/p²)}".

**Formalization Note.** The paper's "smallest set-multilinear" `Φ` must be an arbitrary circuit there,
since it gets set-multilinearized; so this is for every circuit of product-depth at most `Δ` for
`IMM_{n,d}`. The hypotheses are those the proof uses in its range: `M` as in Lemma 7.3 with `c = p`, the
partition condition `2d ≤ log₂ n` of Corollary 2.7, and `d ≤ √n`, which gives `d ≤ n^α̃` as `α̃ > 1/2`.
The constants `K, c₁, n₀` depend only on `Δ`, not on `F` or `p`. There is no `−1` in the exponent: the
bound `s ≥ n`, valid for `d ≥ 2`, covers small `d^{1/R}/p²`. -/
theorem proof_theorem_1_2_bound (Δ : ℕ) (hΔ : 1 ≤ Δ) :
    ∃ K c₁ : ℝ, 0 < K ∧ 0 < c₁ ∧ ∃ n₀ : ℕ,
      ∀ (F : Type u) [Field F] (p : ℕ), p.Prime → ∀ [CharP F p] (n d M : ℕ), n₀ ≤ n → 2 ≤ d →
        200 * p ^ 2 ≤ M → (2 : ℝ) / 3 * (M : ℝ) ^ R Δ ≤ (d : ℝ) → d ≤ M ^ R Δ →
        2 * (d : ℝ) ≤ Real.logb 2 n → (d : ℝ) ≤ √(n : ℝ) →
        ∀ Φ : Circuit (IMMVar n d) F, Φ.value = imm F n d → Φ.HasProductDepthLE Δ →
          (d : ℝ) ^ (-(K * (d : ℝ))) *
              (n : ℝ) ^ (c₁ * (d : ℝ) ^ (1 / (R Δ : ℝ)) / (p : ℝ) ^ 2) ≤ (Φ.size : ℝ) := by sorry

end SetMultCost
