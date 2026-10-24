-- Prove2me | Theorems.Thm_OutlierAssort_ActiveElim_lemma_3
-- name    : OutlierAssort.ActiveElim.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:13.836624+00:00
-- url     : https://prove2.me/theorems/4957980c-8ec4-4f8a-9674-03db5642c0be
-- title:
--   Lemma 3, p. 14 (corrected: line 14 read with min) — if ε̄ ≥ ε then w.p. 1 − O(τ₀N/T²), S* ⊆ A^{(τ)} for all τ
-- statement:
--   Run Algorithm 1 with horizon $T$, input $\bar\varepsilon$, revenues and utilities in $[0,1]$ and capacity $K \ge 1$, against any adaptive adversary sending at most $\varepsilon T$ outliers, where $0 \le \varepsilon \le \bar\varepsilon$, with any argmax tie-break. Let $S^*$ be any optimal assortment for typical customers: $|S^*| \le K$ and $R(S^*;v) = \max_{|S|\le K} R(S;v)$.
--
--   There are universal constants $C$ and $T_1$ such that for $T \ge T_1$, with probability at least $1 - C\tau_0N/T^2$,
--   $$
--   S^* \subseteq \mathcal A^{(\tau)} \quad \text{for every } \tau \le \tau_0 + 1,
--   $$
--   where $\tau_0$ is the last epoch and $\mathcal A^{(\tau_0+1)}$ is the active set sampled from in that epoch.
--
--   The lemma says that elimination never removes an item of an optimal assortment. Lemma 4 builds on this to bound the per-period regret.
--
--   Differences from the source:
--   - correction: Algorithm 1 line 14 $\max\{1, n_i/n_0(i)\}$ → $\min\{1, n_i/n_0(i)\}$, and $1$ when $n_0(i)=0$; reason: the printed rule contradicts $\hat v \in [0,1]^N$ (p. 9) and the proof (ec3), and on $N=2$, $K=1$, $r=(1,1/2)$, $v=(0,1)$, $\varepsilon=\bar\varepsilon=0$ it eliminates the optimal item, so the printed lemma would be false.
--   - reading: "for all $\tau$" → every $\tau \le \tau_0+1$; reason: these are the active sets the run computes and samples from.
--   - reading: "$S^*$" → every optimal assortment; reason: the argmax defining $S^*$ (p. 8) need not be unique.
--   - reading: "with probability $1 - O(\tau_0N/T^2)$" → $\exists\, C, T_1$ placed before all other quantifiers; reason: the stronger of the readings of $O(\cdot)$.
--   - reading: "argmax" in line 5 → every tie-break satisfying the argmax property; reason: the argmax need not be unique.
--   - generalization: outlier distribution $Q_t$ fixed before $S_t$ is offered → $Q_t$ may depend on the offered assortment; reason: the adversary class only grows.
--   - generalization: $\varepsilon \in [0,1)$ → $\varepsilon \ge 0$; reason: the source's range is included.
--   - encoding: $T_0 = 128(K+1)^2N\ln T$ → $\lceil\cdot\rceil$, periods $0,\dots,T-1$, finite sum over records, (A1) on every public record; reason: Lean conventions that keep every run of the source's algorithm.
-- source:
--   Chen, Krishnamurthy, Wang, Robust Dynamic Assortment Optimization in the Presence of Outlier Customers, arXiv:1910.04183v2, p. 14, Lemma 3; proof p. ec5 (PDF 32)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model
import Definitions.Def_OutlierAssort_ActiveElim_Algorithm

namespace OutlierAssort.ActiveElim

/-- Lemma 3 (p. 14): if `ε̄ ≥ ε`, then with probability at least `1 − C τ₀ N / T²` every optimal
assortment `S*` stays inside every active set `A^{(τ)}`, `τ ≤ τ₀ + 1`. -/
theorem lemma_3 :
    ∃ C T1 : ℝ, ∀ (T N K : ℕ), T1 ≤ (T : ℝ) → 1 ≤ N → 1 ≤ K →
      ∀ (r v : Fin N → ℝ), (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (eps epsBar : ℝ), 0 ≤ eps → eps ≤ epsBar →
      ∀ (adv : Adversary N), OutlierBudget adv T eps →
      ∀ (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)), IsArgmaxSel r K sel →
      ∀ (Sstar : Finset (Fin N)), IsOptimal r v K Sstar →
        prob (⟨T, epsBar, r, K, sel⟩ : Input N) v adv
            (fun h => ∃ τ : ℕ, τ ≤ tau0 N K T + 1 ∧
              ¬ Sstar ⊆ (state (⟨T, epsBar, r, K, sel⟩ : Input N) h τ).A) ≤
          C * (tau0 N K T : ℝ) * N / (T : ℝ) ^ 2 := by sorry

end OutlierAssort.ActiveElim
