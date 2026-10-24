-- Prove2me | Theorems.Thm_OutlierAssort_ActiveElim_theorem_1
-- name    : OutlierAssort.ActiveElim.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:39:55.192993+00:00
-- url     : https://prove2.me/theorems/605c7bf1-c1c5-4c48-8777-75c34383a572
-- title:
--   Theorem 1, p. 12 (corrected: (6) assumes K³N log T ≤ c₂T; line 14 read with min) — Algorithm 1 has TOTE regret ≤ C₀(ε̄K²T log T + (K²√ε̄ + √K)√(NT log³T) + K²N log²T)
-- statement:
--   Consider robust dynamic assortment optimization with the following data:
--
--   - $N$ items with revenues $r_i \in [0,1]$ and MNL utilities $v_i \in [0,1]$ (no-purchase weight 1);
--   - capacity $K \ge 1$ and horizon $T \ge N \ge 1$;
--   - an adaptive adversary that sees the whole public past, decides at each period whether the arriving customer is an outlier, and chooses an arbitrary choice distribution for outliers, sending at most $\varepsilon T$ outliers in total.
--
--   Run Algorithm 1 (active elimination, line 14 read with $\min$) with input $\bar\varepsilon \ge \varepsilon \ge 0$ and any tie-break in the argmax of line 5. Measure performance by the TOTE regret
--   $$
--   \mathrm{Regret}_{\mathrm{TOTE}}(T) = \mathbb E\Big[\sum_{t=1}^T R(S^*;v) - R(S_t;v)\Big],
--   $$
--   where $R(S;v) = \sum_{i\in S} r_iv_i/(1+\sum_{i\in S}v_i)$ and $R(S^*;v) = \max_{|S|\le K} R(S;v)$.
--
--   1. There are universal constants $C_0$ and $T_1$ such that for every $T \ge T_1$ and every such instance, adversary and tie-break,
--   $$
--   \mathrm{Regret}_{\mathrm{TOTE}}(T) \le C_0\Big(\bar\varepsilon K^2T\log T + \big(K^2\sqrt{\bar\varepsilon} + \sqrt K\big)\sqrt{NT\log^3T} + K^2N\log^2T\Big).
--   $$
--   2. For all $c_1, c_2 > 0$ there are constants $C$ and $T_1$ such that, if moreover $\bar\varepsilon \le c_1/K^3$ and $K^3N\log T \le c_2T$, then for $T \ge T_1$
--   $$
--   \mathrm{Regret}_{\mathrm{TOTE}}(T) \le C\Big(\bar\varepsilon K^2T\log T + \sqrt{KNT\log^3T}\Big). \qquad (6)
--   $$
--
--   This is the paper's main upper bound: with a known bound on the contamination level, the regret is linear in $\bar\varepsilon T$ (which is unavoidable) plus a $\sqrt{NT}$ term matching the uncontaminated rate up to logarithms.
--
--   **Formalization Note.** The expectation is a finite sum over the records of the run (drawn item, customer type, purchase per period). Each record is weighted by the product of the uniform draw probability, the adversary's type indicator and the purchase probability.
--
--   Differences from the source:
--   - correction: (6) under $\bar\varepsilon \lesssim 1/K^3$ alone → (6) also assumes $K^3N\log T \le c_2T$; reason: as printed (6) is false: with $\varepsilon=\bar\varepsilon=0$, $K = \lceil T^{0.3}\rceil$, $N = 2K$, $K$ items with $(r,v) = (1, 1/K)$ and $K$ items with $(r,v) = (0,1)$, epoch 0 alone costs a constant times $T_0 \asymp T^{0.9}\log T$, more than $C\sqrt{KNT\log^3T} \asymp T^{0.8}\log^{1.5}T$ for every $C$; under the added hypothesis $K^2N\log^2T \le \sqrt{c_2}\sqrt{KNT\log^3T}$ and (6) follows from part 1.
--   - correction: Algorithm 1 line 14 $\max\{1, n_i/n_0(i)\}$ → $\min\{1, n_i/n_0(i)\}$, and $1$ when $n_0(i)=0$; reason: the printed rule forces $\hat v \ge 1$, contradicting $\hat v \in [0,1]^N$ (p. 9) and the proof (ec3); on $N=2$, $K=1$, $r=(1,1/2)$, $v=(0,1)$, $\varepsilon=\bar\varepsilon=0$ it eliminates the optimal item and has regret about $0.25\,T$.
--   - reading: "universal constant $C_0$" and "for sufficiently large $T$" → $\exists\, C_0, T_1$ placed before $T, N, K$, the instance, the adversary and the tie-break; reason: the stronger reading.
--   - reading: "$\bar\varepsilon \lesssim 1/K^3$" and "$O(\cdot)$" in (6) → for all $c_1 > 0$ there are $C, T_1$ with $\bar\varepsilon \le c_1/K^3$ as a hypothesis; reason: the standard meaning of $\lesssim$ with its constant fixed first.
--   - reading: "argmax" in line 5 → every tie-break satisfying the argmax property; reason: the argmax need not be unique.
--   - generalization: outlier distribution $Q_t$ fixed before $S_t$ is offered → $Q_t$ may depend on the offered assortment; reason: the adversary class only grows, so the bound over all adversaries specializes to the source's.
--   - generalization: $\varepsilon \in [0,1)$ → $\varepsilon \ge 0$; reason: the source's range is included.
--   - encoding: $T_0 = 128(K+1)^2N\ln T$ → $\lceil\cdot\rceil$, the last epoch truncated at $T$, periods $0,\dots,T-1$, outcomes `Option (Fin N)`, the expectation as a finite sum over records, (A1) on every public record, $\log = \ln$; reason: Lean conventions that keep every run of the source's algorithm.
-- source:
--   Chen, Krishnamurthy, Wang, Robust Dynamic Assortment Optimization in the Presence of Outlier Customers, arXiv:1910.04183v2, p. 12, Theorem 1, (6); proof pp. 14–15

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model
import Definitions.Def_OutlierAssort_ActiveElim_Algorithm

namespace OutlierAssort.ActiveElim

/-- Theorem 1 (p. 12). (a) There are universal `C₀` and `T₁` such that for `T ≥ T₁`, `1 ≤ N ≤ T`,
`K ≥ 1`, `r, v ∈ [0, 1]^N`, `0 ≤ ε ≤ ε̄`, every adaptive adversary with at most `ε T` outliers and
every argmax tie-break, the TOTE regret of Algorithm 1 is at most
`C₀ (ε̄ K² T log T + (K² √ε̄ + √K) √(N T log³ T) + K² N log² T)`.
(b) (6), corrected: for all `c₁, c₂ > 0` there are `C` and `T₁` such that, if moreover
`ε̄ ≤ c₁ / K³` and `K³ N log T ≤ c₂ T`, the regret is at most `C (ε̄ K² T log T + √(K N T log³ T))`. -/
theorem theorem_1 :
    (∃ C0 T1 : ℝ, ∀ (T N K : ℕ), T1 ≤ (T : ℝ) → 1 ≤ N → N ≤ T → 1 ≤ K →
      ∀ (r v : Fin N → ℝ), (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (eps epsBar : ℝ), 0 ≤ eps → eps ≤ epsBar →
      ∀ (adv : Adversary N), OutlierBudget adv T eps →
      ∀ (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)), IsArgmaxSel r K sel →
        toteRegret (⟨T, epsBar, r, K, sel⟩ : Input N) v adv ≤
          C0 * (epsBar * K ^ 2 * T * Real.log T +
            (K ^ 2 * Real.sqrt epsBar + Real.sqrt K) * Real.sqrt (N * T * Real.log T ^ 3) +
            K ^ 2 * N * Real.log T ^ 2)) ∧
    (∀ c1 c2 : ℝ, 0 < c1 → 0 < c2 →
      ∃ C T1 : ℝ, ∀ (T N K : ℕ), T1 ≤ (T : ℝ) → 1 ≤ N → N ≤ T → 1 ≤ K →
      ∀ (r v : Fin N → ℝ), (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (eps epsBar : ℝ), 0 ≤ eps → eps ≤ epsBar →
      ∀ (adv : Adversary N), OutlierBudget adv T eps →
      ∀ (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)), IsArgmaxSel r K sel →
        epsBar ≤ c1 / (K : ℝ) ^ 3 → (K : ℝ) ^ 3 * N * Real.log T ≤ c2 * T →
        toteRegret (⟨T, epsBar, r, K, sel⟩ : Input N) v adv ≤
          C * (epsBar * K ^ 2 * T * Real.log T + Real.sqrt (K * N * T * Real.log T ^ 3))) := by sorry

end OutlierAssort.ActiveElim
