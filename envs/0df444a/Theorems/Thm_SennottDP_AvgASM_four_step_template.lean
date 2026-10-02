-- Prove2me | Theorems.Thm_SennottDP_AvgASM_four_step_template
-- name    : SennottDP.AvgASM.four_step_template
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T09:40:19.08932+00:00
-- url     : https://prove2.me/theorems/bf0654d3-9e63-4d5b-8666-be5993bae390
-- title:
--   Proposition 8.2.1 — the four step template verifies the VIA and the (AC) assumptions
-- statement:
--   Let $(\Delta_N)_{N\ge N_0}$ be an approximating sequence for the MDC $\Delta$, and let $x$ be a distinguished state with $x\in S_N$ for all $N$. Suppose the following four steps can be carried out.
--
--   1. **Step 1.** Every stationary policy for $\Delta_N$ induces a unichain Markov chain with aperiodic positive recurrent class containing $x$.
--   2. **Step 2.** There is an $x$ standard policy $d$ for $\Delta$ such that the AS is conforming at $d$.
--   3. **Step 3.** One of: (i) $v^N_n(i)\le v_n(i)$ for all $n$, $N$ and $i\in S_N$; (ii) $V^N_\alpha(i)\le V_\alpha(i)$ for all $\alpha\in(0,1)$, $N$ and $i\in S_N$; (iii) the minimum average cost in $\Delta$ is constant, and some average cost optimal stationary policy $f$ induces a Markov chain with a positive recurrent class $R_f$ (of finite average cost) on which the AS is conforming.
--   4. **Step 4.** One of: (i) $v^N_n(i)\ge v^N_n(x)$ for all $n$, $N$, $i\in S_N$; (ii) $V^N_\alpha(i)\ge V^N_\alpha(x)$ for all $\alpha\in(0,1)$, $N$, $i\in S_N$; (iii) some nonempty finite set $G$ contains a minimum point of $v^N_n$ for all $n$ and $N$, and some stationary policy $g$ induces a Markov chain with a positive recurrent class $R_g\supseteq G\cup\{x\}$ of finite average cost on which the AS is conforming; (iv) the same as (iii) with $V^N_\alpha$, for all $N$ and $\alpha\in(0,1)$, in place of $v^N_n$.
--
--   Then the value iteration algorithm is justified in every $\Delta_N$, and the (AC) assumptions hold for
--   $$r^N(i)=\lim_{n\to\infty}\big(v^N_n(i)-v^N_n(x)\big),\qquad J^N=\lim_{n\to\infty}\big(v^N_{n+1}(x)-v^N_n(x)\big).$$
--
--   This template is the standard way the (AC) assumptions, and hence Theorem 8.1.1, are verified in queueing models.
--
--   **Formalization Note** The conclusion is the existence of the two limits in every $\Delta_N$ together with (AC1)–(AC4) for them. "Conforming on $R$" includes that $R$ is a positive recurrent class with finite average cost, as Definition C.4.10 presupposes.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 171–172, Proposition 8.2.1

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Proposition 8.2.1** (Sennott 1999, pp. 171–172), the four step template. Let `(Δ_N)` be an
AS for `Δ` and `x` a distinguished state with `x ∈ S_N` for all `N ≥ N₀`. Assume
* Step 1: every stationary policy for `Δ_N` induces a unichain MC with aperiodic positive
  recurrent class containing `x`;
* Step 2: there is an `x` standard policy `d` for `Δ` such that the AS is conforming at `d`;
* Step 3: one of (i) `v^N_n(i) ≤ v_n(i)`; (ii) `V^N_α(i) ≤ V_α(i)` for `α ∈ (0,1)`; (iii) the
  minimum average cost in `Δ` is constant and some average cost optimal stationary `f` induces an
  MC with a positive recurrent class `R_f` (with finite average cost) on which the AS is
  conforming;
* Step 4: one of (i) `v^N_n(i) ≥ v^N_n(x)`; (ii) `V^N_α(i) ≥ V^N_α(x)` for `α ∈ (0,1)`;
  (iii)/(iv) a nonempty finite set `G` contains a minimizer of `v^N_n` for all `n, N` (resp. of
  `V^N_α` for all `N`, `α ∈ (0,1)`), and a stationary `g` induces an MC with a positive recurrent
  class `R_g ⊇ G ∪ {x}` with finite average cost on which the AS is conforming.
Then the value iteration algorithm is justified in each `Δ_N` and the (AC) assumptions hold for
`r^N(·) = lim_{n→∞} (v^N_n(·) − v^N_n(x))`. -/
theorem four_step_template {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (x : S) (hx : ∀ N, AS.N₀ ≤ N → x ∈ AS.SN N)
    (step1 : ∀ N (hN : AS.N₀ ≤ N), ∀ e : StationaryPolicy (AS.toMDC N hN),
      IsUnichainAperiodicWith e.chain ⟨x, hx N hN⟩)
    (step2 : ∃ d : StationaryPolicy M, IsStandard d.chain d.cost x ∧ AS.IsConformingAt d x)
    (step3 :
      (∀ n N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, AS.valueN n N i ≤ horizonValue M n i) ∨
      (∀ α : ℝ, 0 < α → α < 1 → ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N,
        AS.discValueN α N i ≤ discValue M α i) ∨
      ((∃ J : ℝ≥0∞, ∀ i, avgValue M i = J) ∧
        ∃ (f : StationaryPolicy M) (Rf : Set S), IsAverageOptimal f.toPolicy ∧
          AS.IsConformingOn f Rf))
    (step4 :
      (∀ n N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, AS.valueN n N x ≤ AS.valueN n N i) ∨
      (∀ α : ℝ, 0 < α → α < 1 → ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N,
        AS.discValueN α N x ≤ AS.discValueN α N i) ∨
      (∃ G : Finset S, G.Nonempty ∧
        (∀ n N, AS.N₀ ≤ N → ∃ k ∈ G, k ∈ AS.SN N ∧
          ∀ i ∈ AS.SN N, AS.valueN n N k ≤ AS.valueN n N i) ∧
        ∃ (g : StationaryPolicy M) (Rg : Set S), (↑G ∪ {x} : Set S) ⊆ Rg ∧
          AS.IsConformingOn g Rg) ∨
      (∃ G : Finset S, G.Nonempty ∧
        (∀ α : ℝ, 0 < α → α < 1 → ∀ N, AS.N₀ ≤ N → ∃ k ∈ G, k ∈ AS.SN N ∧
          ∀ i ∈ AS.SN N, AS.discValueN α N k ≤ AS.discValueN α N i) ∧
        ∃ (g : StationaryPolicy M) (Rg : Set S), (↑G ∪ {x} : Set S) ⊆ Rg ∧
          AS.IsConformingOn g Rg)) :
    AS.VIAAndAC x := by sorry

end SennottDP.AvgASM
