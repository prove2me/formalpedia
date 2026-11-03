-- Prove2me | Theorems.Thm_SalesEffort_theorem_1
-- name    : SalesEffort.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:37.595454+00:00
-- url     : https://prove2.me/theorems/efcc27cd-13ac-4791-9a6f-28334c947b0d
-- title:
--   Theorem 1, pp.11–12 — the watershed structure of the optimal policy (corrected: $\lim_{t\to0}\lambda^*(t,1)$ is the maximizer of $\lambda b-c(\lambda)$)
-- statement:
--   Let the model satisfy Assumption 1, let $J$ solve the HJB system (2) with its boundary conditions on $t\ge0$, write $\Delta_t(n)=J_t(n-1)-J_t(n)$ (with $\Delta_t(0)=p$), and let $\lambda^*(t,n)$ be the maximizing rate at $\Delta_t(n)$. "Increase" and "decrease" are weak.
--
--   1. $J_t(n)$ increases in $t\ge0$ and decreases in $n\ge0$.
--   2. If $b>p$, there is a function $\tau$ with $0=\tau(1)<\tau(2)<\cdots$ (all $\tau(n)$ finite and $\ge0$) such that for every $n\ge1$:
--      - (a) on $t>\tau(n)$, $\Delta_t(n)$ and $\lambda^*(t,n)$ decrease in $t$; and for each such $t$, $\Delta_t(m)$ and $\lambda^*(t,m)$ increase in $m$ for $0\le m\le n$;
--      - (b) on $0\le t\le\tau(n)$, $\Delta_t(n)$ and $\lambda^*(t,n)$ increase in $t$; and for each such $t$, $\Delta_t(m)$ and $\lambda^*(t,m)$ decrease in $m\ge n$.
--   3. If $b\le p$, $\Delta_t(n)$ and $\lambda^*(t,n)$ increase in $t\ge0$ for every $n\ge1$, and decrease in $n\ge0$ for every $t\ge0$.
--   4. $\displaystyle\lim_{t\to\infty}\lambda^*(t,n)=\lambda^*$ for every $n\ge0$; $\displaystyle\lim_{t\to0^+}\lambda^*(t,n)=\underline\lambda$ for every $n\ge2$; and $\displaystyle\lim_{t\to0^+}\lambda^*(t,1)=\arg\max_{\lambda\in[\underline\lambda,\bar\lambda]}\{\lambda b-c(\lambda)\}$.
--
--   When the bonus outweighs the commission, the optimal sales effort for each backlog $n$ rises and then falls in the time to go, with a watershed $\tau(n)$ that moves later as the backlog grows; otherwise effort only rises with time to go.
--
--   **Formalization Note** $\tau:\mathbb N\to\mathbb R$ is one function for all $n$; (a) holds on the open ray $(\tau(n),\infty)$ and (b) on $[0,\tau(n)]$. $t\to0$ is the right limit.
--
--   Differences from the source:
--   - reading: Assumption 1(ii): c(λ) is invertible, and convex on [λ̲, λ̄] (with the proof's α = min c″ > 0, OA p.5) → c is continuous, injective and α-strongly convex on [λ̲, λ̄] for some α > 0; reason: the paper's 'regularity conditions specified in Assumption 1' (p.11) that make λ∗(t,n) unique; with convexity alone the arg max need not be unique (c(λ) = λ − 1 on [1, 3], p = 1)
--   - generalization: the proof uses c′ and c″ with min c″ = α > 0 on [λ̲, λ̄] → no derivative of c is assumed; reason: every C² cost with c″ ≥ α > 0 on [λ̲, λ̄] is α-strongly convex there, so the statement specializes to the source's
--   - reading: λ∗ = arg max{λ | λp − c(λ)} with λ∗ ∈ [λ̲, λ̄] (Assumption 1(iii)) → λ∗ is a maximizer of λp − c(λ) over [λ̲, λ̄]; reason: [λ̲, λ̄] is the feasible set of rates; the maximizer is unique by strong convexity, and an unconstrained arg max lying in [λ̲, λ̄] is this one
--   - encoding: J∗_t(n), the optimal expected profit, which is the solution of (2) with its boundary conditions, ∀t → any J solving (2) with both boundary conditions on t ∈ [0, ∞): derivative within [0, ∞) at every t ≥ 0 (one-sided at 0) equal to the attained maximum; reason: Theorem 1's proof uses only (2); Proposition 1 (a milestone) gives exactly one such solution on t ≥ 0; t is the time to go
--   - encoding: λ∗(t,n), the unique maximizer of λ∆_t(n) − c(λ) over [λ̲, λ̄] → any function lam with lam t n such a maximizer for every t ≥ 0 and n ≥ 0; reason: the maximizer is unique, so lam is λ∗(t,n) on t ≥ 0; at n = 0 it is λ∗, the paper's λ∗(t,0) = λ∗ (OA p.4)
--   - encoding: ∆_t(n) := J∗_t(n−1) − J∗_t(n), and J∗_t(−1) = J∗(0) + p (OA p.2) → marginal M J t n, equal to p at n = 0; reason: the paper's own convention ∆_t(0) = p
--   - reading: increases / decreases → weak monotonicity (MonotoneOn / AntitoneOn); 'τ(n) strictly increases' strict; reason: the proof says 'weak monotonicity' (OA p.4); the strict reading is false (λ∗(t,n) is clamped at λ̲, and J_0(n) = 0 for all n ≥ 1)
--   - correction: lim_{t→0} λ∗(t,n) = λ̲, ∀n > 0 → for n ≥ 2; and for n = 1 the limit is the maximizer of λb − c(λ) over [λ̲, λ̄]; reason: ∆_0(1) = b, so λ∗(t,1) tends to that maximizer, which is not λ̲ in general: c(λ) = (λ−2)², λ̲ = 2, λ̄ = 10, b = 40, p = 2 (Figure 1's data) give the limit 10
--   - generalization: ∆_t(m), λ∗(t,m) increase in m for any m ≤ n (ii)(a); decrease in n (iii) → m ranges over 0 ≤ m ≤ n, and n over n ≥ 0, with ∆_t(0) = p and λ∗(t,0) = λ∗; reason: contains the printed range m, n ≥ 1, on which ∆_t(m) is defined in the main text
--   - encoding: there exists 0 ≤ τ(n) < ∞, ∀n ≥ 1; when t > τ(n) / t ≤ τ(n); lim_{t→0} → τ : ℕ → ℝ with τ 1 = 0, τ n ≥ 0 and τ n < τ (n+1) for n ≥ 1; (a) on Ioi (τ n), (b) on Icc 0 (τ n); 𝓝[>] 0; reason: real-valued τ is finite; t is the time to go
-- source:
--   Du, Hu & Wu, Sales Effort Management under All-or-Nothing Constraint, SSRN 3506499 (University of Toronto TSpace submitted manuscript), https://ssrn.com/abstract=3506499, Theorem 1, pp.11–12 (PDF 12–13); proof Online Appendix pp.2–5 (PDF 36–39)

import Mathlib
import Definitions.Def_SalesEffort_Model

open Set Filter Topology

namespace SalesEffort

/-- **Theorem 1 (Watershed Structure of Optimal Policy)**, Du, Hu & Wu, *Sales Effort Management
under All-or-Nothing Constraint*, SSRN 3506499, pp.11–12 (proof Online Appendix pp.2–5):

(i) `J∗_t(n)` increases in `t` but decreases in `n`;
(ii) when `b > p`, there exists `0 ≤ τ(n) < ∞`, `∀n ≥ 1`, such that
  (a) when `t > τ(n)`, `∆t(n)` and `λ∗(t,n)` decrease in `t`; `∆t(m)` and `λ∗(t,m)` increase in
      `m`, for any `m ≤ n`;
  (b) when `t ≤ τ(n)`, `∆t(n)` and `λ∗(t,n)` increase in `t`; `∆t(m)` and `λ∗(t,m)` decrease in
      `m`, for any `m ≥ n`;
  moreover `0 = τ(1) < τ(2) < ⋯`;
(iii) when `b ≤ p`, `∆t(n)` and `λ∗(t,n)` increase in `t` and decrease in `n`;
(iv) `lim_{t→∞} λ∗(t,n) = λ∗`, `∀n ≥ 0`, and `lim_{t→0} λ∗(t,n) = λ̲`, `∀n > 0`.

**Formalization Note.**
1. `J` is any solution of the HJB system (2) with its boundary conditions on `t ∈ [0, ∞)`
   (Proposition 1 gives exactly one); `lam` is any profit-maximizing rate function of `J`, the
   paper's `λ∗(t,n)` (unique on `t ≥ 0`).
2. "Increase"/"decrease" are weak (`MonotoneOn`/`AntitoneOn`), as the proof says ("weak
   monotonicity", Online Appendix p.4); `τ(n) strictly increases` is strict.
3. One cutoff function `τ : ℕ → ℝ` serves every `n ≥ 1`; (a) is on `t ∈ (τ(n), ∞)`, (b) on
   `t ∈ [0, τ(n)]`; the `m`-clauses hold for each fixed `t` in that range.
4. `∆_t(0) = p` and `λ∗(t,0) = λ∗` (Online Appendix pp.2, 4); the `m`-clauses of (a) and (iii) are
   stated with `m = 0` included (`Icc 0 n`, `Ici 0`), which contains the printed `m ≥ 1` range.
5. Correction to (iv): `lim_{t→0} λ∗(t,n) = λ̲` holds for `n ≥ 2`; for `n = 1`, `∆_0(1) = b` and
   `λ∗(t,1)` tends to the maximizer of `λb − c(λ)` over `[λ̲, λ̄]`, which is not `λ̲` in general
   (`c(λ) = (λ−2)²`, `λ̲ = 2`, `λ̄ = 10`, `b = 40`, `p = 2`: the limit is `10`). `t → 0` is `t → 0⁺`. -/
theorem theorem_1 (M : Model) (J : ℝ → ℕ → ℝ) (hJ : IsHJBSolution M J)
    (lam : ℝ → ℕ → ℝ) (hlam : IsRateFn M J lam) :
    -- (i)
    ((∀ n : ℕ, MonotoneOn (fun t => J t n) (Ici 0)) ∧
      (∀ t : ℝ, 0 ≤ t → Antitone (fun n : ℕ => J t n))) ∧
    -- (ii)
    (M.p < M.b → ∃ τ : ℕ → ℝ, τ 1 = 0 ∧ (∀ n : ℕ, 1 ≤ n → 0 ≤ τ n) ∧
      (∀ n : ℕ, 1 ≤ n → τ n < τ (n + 1)) ∧
      ∀ n : ℕ, 1 ≤ n →
        -- (a)
        (AntitoneOn (fun t => marginal M J t n) (Ioi (τ n)) ∧
          AntitoneOn (fun t => lam t n) (Ioi (τ n)) ∧
          ∀ t : ℝ, τ n < t →
            MonotoneOn (fun m : ℕ => marginal M J t m) (Icc 0 n) ∧
            MonotoneOn (fun m : ℕ => lam t m) (Icc 0 n)) ∧
        -- (b)
        (MonotoneOn (fun t => marginal M J t n) (Icc 0 (τ n)) ∧
          MonotoneOn (fun t => lam t n) (Icc 0 (τ n)) ∧
          ∀ t ∈ Icc 0 (τ n),
            AntitoneOn (fun m : ℕ => marginal M J t m) (Ici n) ∧
            AntitoneOn (fun m : ℕ => lam t m) (Ici n))) ∧
    -- (iii)
    (M.b ≤ M.p →
      (∀ n : ℕ, 1 ≤ n →
        MonotoneOn (fun t => marginal M J t n) (Ici 0) ∧ MonotoneOn (fun t => lam t n) (Ici 0)) ∧
      ∀ t : ℝ, 0 ≤ t →
        AntitoneOn (fun m : ℕ => marginal M J t m) (Ici 0) ∧
        AntitoneOn (fun m : ℕ => lam t m) (Ici 0)) ∧
    -- (iv)
    (∀ n : ℕ, Tendsto (fun t => lam t n) atTop (𝓝 M.lstar)) ∧
    (∀ n : ℕ, 2 ≤ n → Tendsto (fun t => lam t n) (𝓝[>] 0) (𝓝 M.lo)) ∧
    (∀ ℓb : ℝ, IsOptRate M M.b ℓb → Tendsto (fun t => lam t 1) (𝓝[>] 0) (𝓝 ℓb)) := by sorry

end SalesEffort
