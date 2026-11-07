-- Prove2me | Theorems.Thm_UncrowdedColoring_lemma_4_1
-- name    : UncrowdedColoring.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:13:15.886642+00:00
-- url     : https://prove2.me/theorems/e00613c3-b941-41bc-9464-2eb97b199a40
-- title:
--   Lemma 4.1 — bounds (S1)–(S6) on the parameters
-- statement:
--   Let $k\ge 2$, $0<\varepsilon<1$, and let $\eta,\alpha,s,t_i,q_i,\beta_i,\gamma_i,\mathrm{keep}_i,\mathrm{uncolor}_i$ be as in (13)–(17). There are $c>0$ and $d_0$ such that for $d\ge d_0$ and $i\in[s-1]$:
--
--   1. (S1) $\gamma_1=0$ and $1\le\gamma_{i+1}\le\log d/(\eta(1-\eta))$;
--   2. (S2) $1-\eta\le\mathrm{keep}_i$ and $1-\mathrm{keep}_i\ge c(\log d)^{-k}$;
--   3. (S3) $1-\alpha\le\mathrm{uncolor}_i\le 1-\alpha(1-\eta)$;
--
--   and for $i\in[s]$:
--
--   4. (S4) $(\log d)^{-2}\le\beta_i\le(1-\alpha(1-\eta))^{i-1}$;
--   5. (S5) $\displaystyle\frac{\log d}{(1+\varepsilon)^{k-1}(k-1)}\le\frac{t_i}{q_i^{k-1}}\le\frac{\log d}{(1+5\eta)^{k-1}(k-1)}$;
--   6. (S6) $q_i\gg d^{\eta/(k-1)}$: for every $K$ there is $d_K$ with $q_i\ge Kd^{\eta/(k-1)}$ for all $d\ge d_K$, $i\in[s]$.
--
--   These purely numerical facts drive every estimate in the iteration.
--
--   Differences from the source:
--   - generalization: d ≥ d_0 with d_0 ∈ ℕ, d read as an integer → d : ℝ with (d₀ : ℝ) ≤ d; reason: §7, eq. (81), p.53 applies the results at a non-integer d; natural d is a cast
--   - encoding: keep_i = 1 − Ω((log d)^{−k}) and q_i ≫ d^{η/(k−1)} → ∃ c > 0 before d₀ with 1 − keep_i ≥ c (log d)^{−k}; ∀ K ∃ d₀ with K d^{η/(k−1)} ≤ q_i, uniformly in i; reason: the convention of §3.1, p.14
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Lemma 4.1, p.17

import Mathlib
import Definitions.Def_UncrowdedColoring_paramState

namespace UncrowdedColoring

/-- **Lemma 4.1, (S1)–(S6)**, p.17.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Lemma 4.1, p.17, with the parameters (13)–(17), p.16.

**Formalization Note.** `k ≥ 2` and `0 < ε < 1` are the standing assumptions of §4 (p.16), and `d` is
real with `d ≥ d₀(k, ε)`. The Ω in (S2) is unfolded with the constant `c` before `d₀`:
`1 − keep_i ≥ c (log d)^{−k}` (p.14: implicit constants depend only on the fixed parameters `k`, `ε`).
`q_i ≫ d^{η/(k−1)}` in (S6) is uniform in `i`: for every `K` there is `d_K` with
`q_i ≥ K d^{η/(k−1)}` for all `d ≥ d_K` and all `i ∈ [s]`. -/
theorem lemma_4_1 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    (∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d →
      (∀ i : ℕ, 1 ≤ i → i + 1 ≤ numSteps ε d →
        -- (S1)
        (gammaSeq k ε d 1 = 0 ∧ 1 ≤ gammaSeq k ε d (i + 1) ∧
          gammaSeq k ε d (i + 1) ≤ Real.log d / (eta ε * (1 - eta ε))) ∧
        -- (S2)
        (1 - eta ε ≤ keep k ε d i ∧ c * Real.log d ^ (-(k : ℤ)) ≤ 1 - keep k ε d i) ∧
        -- (S3)
        (1 - alpha ε d ≤ uncolor k ε d i ∧
          uncolor k ε d i ≤ 1 - alpha ε d * (1 - eta ε))) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ numSteps ε d →
        -- (S4)
        (Real.log d ^ (-2 : ℤ) ≤ betaSeq k ε d i ∧
          betaSeq k ε d i ≤ (1 - alpha ε d * (1 - eta ε)) ^ (i - 1)) ∧
        -- (S5)
        (Real.log d / ((1 + ε) ^ (k - 1) * ((k : ℝ) - 1)) ≤
            tSeq k ε d i / qSeq k ε d i ^ (k - 1) ∧
          tSeq k ε d i / qSeq k ε d i ^ (k - 1) ≤
            Real.log d / ((1 + 5 * eta ε) ^ (k - 1) * ((k : ℝ) - 1))))) ∧
    -- (S6)
    ∀ K : ℝ, ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d → ∀ i : ℕ, 1 ≤ i → i ≤ numSteps ε d →
      K * d ^ (eta ε / ((k : ℝ) - 1)) ≤ qSeq k ε d i := by sorry

end UncrowdedColoring
