-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_theorem_7_1
-- name    : SparseSDP.TwoSided.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:58:49.844923+00:00
-- url     : https://prove2.me/theorems/92a75704-6c6c-4114-a767-608a5eb91f12
-- title:
--   Theorem 7.1, pp. 44–45 — the game solver: gap $O(Rr\omega\sqrt{\Lambda/T})$ and running time
-- statement:
--   Let $A_j\in\mathbb R^{n\times n}$ be real symmetric, $s$-row-sparse, with $\|A_j\|\le\omega$. Define $\gamma=Rr\omega/\varepsilon$, with $0<\varepsilon\le Rr\omega$, and $\Lambda=\log(16mn/\delta)$. Run Algorithm 7 for $T$ rounds. With probability at least $1-\delta$,
--   $$
--   \mathrm{Gap}(X^{\mathrm{out}},z^{\mathrm{out}})\le O\Big(Rr\omega\sqrt{\frac\Lambda T}\Big).
--   $$
--   Thus $T=O(\gamma^2\Lambda)$ rounds suffice for an $\varepsilon$-accurate saddle point, with running time
--   $$
--   \tilde O\big(ns\min\{\gamma^2,m,n/s\}\gamma^{5/2}+(n+ms)\gamma^2\big).
--   $$
--
--   The Lean statement has three clauses, with $C_L$ sufficiently large: the gap bound for every $T\ge1$ with a constant $C_1$; for every round constant $C_T'\ge C_1^2$, the bound $\mathrm{Gap}\le\varepsilon$ at $T=\lceil C_T'\gamma^2\Lambda\rceil$; and, at $T=\lceil C_T\gamma^2\Lambda\rceil$ for the constant $C_T$ of `Consts`, the cost bound on every tape, with $\tilde O$ a constant times $L^\kappa$, $L=\log(2+n+m+\gamma+1/\delta)$.
--
--   This is the algorithmic core: both players update from one sample per round.
--
--   Differences from the source:
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $T=O(\gamma^2\Lambda)$ → $C_1$ chosen after `Consts`; $C,\kappa$ depending on `Consts` and the row-read constant; $\tilde O(f)=C f L^\kappa$; $T=\lceil C_T\gamma^2\Lambda\rceil$, for every $C_T\ge C_1^2$ in the accuracy clause; reason: the constants come before the instance; every logarithm of the proof is a polylogarithm of $L$
--   - reading: running time → the operation count of the program `alg7` on every tape; reason: $T$ and $k_t$ are deterministic, so the worst case is what the proof gives
--   - reading: Algorithm 7 with sparse oracle access → a `RowAccess` with `Spec` constant $c$; reason: row access is all the runtime proof uses, and it covers the derived matrices of Corollary 7.11
--   - encoding: with probability at least $1-p$ → the failure set has outer measure at most $p$ under `tapeLaw`; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Theorem 7.1, pp. 44–45, Eqs. (226), (227); Eq. (39), p. 17

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Trajectory

open Matrix MeasureTheory

namespace SparseSDP.TwoSided

/-- **Theorem 7.1** (Main theorem for sampled sparse-oracle SDP solving), pp. 44–45.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Theorem 7.1, pp. 44–45.

Three clauses, for `γ = Rrω/ε ≥ 1`, `Λ = log(16kd/δ)`, with `k` constraints in dimension `d`:

1. Eq. (226): for every `T ≥ 1`, except with probability `δ`, `Gap(X^out, z^out) ≤ C₁Rrω√(Λ/T)`.
2. For every round constant `C_T' ≥ C₁²`, at `T = ⌈C_T' γ²Λ⌉`, except with probability `δ`,
   `Gap ≤ ε` ("`T = O(γ²Λ)` rounds suffice"). `C_T'` is quantified after `C₁`, so the clause is
   not vacuous; Algorithm 7 does not read `P.CT`.
3. Eq. (227): the cost at `T = ⌈P.CT γ²Λ⌉` (any `C_T > 0`), on every tape, is `Õ(ds min{γ², k, d/s}γ^{5/2} + (d + ks)γ²)`,
   with `Õ` a constant `C` times `L^κ`, `L = log(2 + d + k + γ + 1/δ)`; `C` depends on the row-read
   constant `c` and on `P`.

`C₁` is chosen after `P` (the `C′` of Eq. (348) depends on the `Θ` constants of Algorithm 7); `C_L`
is sufficiently large. -/
theorem theorem_7_1 : ∃ C₀ : ℝ, ∀ (P : Consts), C₀ ≤ P.CL →
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ c : ℝ, ∃ (C : ℝ) (κ : ℕ), 0 < C ∧
    ∀ {d k : ℕ} [NeZero d] [NeZero k] (M : Fin k → Mat d) (acc : RowAccess d k) (s : ℕ)
      (ω R r ε δ : ℝ), Alg7Hyp M acc s c ω R r δ → 0 < ε → ε ≤ R * r * ω →
      (∀ T : ℕ, 1 ≤ T →
        tapeLaw {tape | ¬ gap M R r (Xout R (traj P acc s ω R r T δ tape))
            (zout r (traj P acc s ω R r T δ tape)) ≤
          C₁ * (R * r * ω) * √(lamP k d δ / T)} ≤ ENNReal.ofReal δ) ∧
      (∀ CT' : ℝ, C₁ ^ 2 ≤ CT' →
        tapeLaw {tape | ¬ gap M R r
            (Xout R (traj P acc s ω R r ⌈CT' * (R * r * ω / ε) ^ 2 * lamP k d δ⌉₊ δ tape))
            (zout r (traj P acc s ω R r ⌈CT' * (R * r * ω / ε) ^ 2 * lamP k d δ⌉₊ δ tape)) ≤
          ε} ≤ ENNReal.ofReal δ) ∧
      ∀ tape : Tape,
        (runCost (alg7 P acc s ω R r ⌈P.CT * (R * r * ω / ε) ^ 2 * lamP k d δ⌉₊ δ) tape : ℝ) ≤
          C * ((d : ℝ) * s * min ((R * r * ω / ε) ^ 2) (min (k : ℝ) ((d : ℝ) / s)) *
                (R * r * ω / ε) ^ (5 / 2 : ℝ) +
              ((d : ℝ) + k * s) * (R * r * ω / ε) ^ 2) *
            polyL d k (R * r * ω / ε) δ ^ κ := by sorry

end SparseSDP.TwoSided
