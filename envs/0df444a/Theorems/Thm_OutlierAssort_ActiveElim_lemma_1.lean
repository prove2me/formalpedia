-- Prove2me | Theorems.Thm_OutlierAssort_ActiveElim_lemma_1
-- name    : OutlierAssort.ActiveElim.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:39:59.931618+00:00
-- url     : https://prove2.me/theorems/158c9785-62ca-496b-9b20-ae2efc8338ad
-- title:
--   Lemma 1, p. 13 (corrected: line 14 read with min) — w.p. 1 − O(τ₀N/T²), |v̂ᵢ^{(τ+1)} − vᵢ| ≤ ∆*_ε(i, τ+1) on every completed epoch with min{1, εT/T_τ} ≤ 1/(4(K+2))
-- statement:
--   Run Algorithm 1 with horizon $T$, input $\bar\varepsilon \ge 0$, revenues and utilities in $[0,1]$ and capacity $K \ge 1$, against any adaptive adversary that sends at most $\varepsilon T$ outlier customers, with any tie-break in the argmax of line 5. For a completed epoch $\tau$ write
--
--   - $T_\tau = 2^\tau T_0$ for its length;
--   - $\varepsilon_\tau = \min\{1, \varepsilon T/T_\tau\}$, with the true outlier proportion $\varepsilon$;
--   - $N_\tau = |\mathcal A^{(\tau+1)}|$;
--   - $V_S = \sum_{j \in S_\tau^{(i)}} v_j$ for the true utility mass of the assortment offered for item $i$.
--
--   Define
--   $$
--   \Delta^*_\varepsilon(i, \tau+1) = 8(K+1)\Big(\frac{\varepsilon_\tau}{2} + \sqrt{\frac{\varepsilon_\tau N_\tau \ln T}{T_\tau}} + \frac{2N_\tau\ln T}{3T_\tau}\Big) + 8\sqrt{\frac{(1+V_S)\, v_i N_\tau \ln T}{T_\tau}}. \qquad (7)
--   $$
--   There are universal constants $C$ and $T_1$ such that for all $T \ge T_1$ the following holds with probability at least $1 - C(\tau_0+1) N/T^2$, where $\tau_0$ is the index of the last epoch (so there are $\tau_0 + 1$ epochs). For every completed epoch $\tau$ with $\varepsilon_\tau \le 1/(4(K+2))$ and every $i \in \mathcal A^{(\tau+1)}$,
--   $$
--   \big|\hat v^{(\tau+1)}_i - v_i\big| \le \Delta^*_\varepsilon(i,\tau+1).
--   $$
--
--   This is the estimation-error lemma on which the elimination step rests: Corollary 1 turns it into a bound on the revenue error of every candidate assortment.
--
--   **Formalization Note.** The probability is the mass of the bad event under the law of the run. The condition $T_0 \ge 128(K+1)^2N_\tau\ln T$ holds by the definition of $T_0$, since $N_\tau \le N$. An epoch is completed when it ends by period $T$; the truncated last epoch has fewer than $T_\tau$ samples and is not covered.
--
--   Differences from the source:
--   - correction: Algorithm 1 line 14 $\hat v_i = \max\{1, n_i/n_0(i)\}$ → $\min\{1, n_i/n_0(i)\}$, and $1$ when $n_0(i)=0$; reason: the printed $\max$ forces $\hat v \ge 1$, contradicting $\hat v\in[0,1]^N$ (p. 9) and the proof (ec3); on $N=2$, $K=1$, $r=(1,1/2)$, $v=(0,1)$, $\varepsilon=\bar\varepsilon=0$ the printed rule eliminates the optimal item.
--   - generalization: the lemma is restricted to epochs with $T_\tau \ge \max\{\bar\varepsilon,\varepsilon\}T/4(K+1)$ → no such restriction; reason: the proof (ec2–ec3) never uses $\bar\varepsilon$, and the $\varepsilon$ part is implied by $\varepsilon_\tau \le 1/(4(K+2)) < 1$; dropping a restriction proves the bound on more epochs.
--   - reading: $\min\{1,\varepsilon T/T_\tau\} \le 1/4(K+2)$ as a global hypothesis → $\varepsilon_\tau \le 1/(4(K+2))$ imposed per epoch; reason: the quantity depends on $\tau$, and the proof uses it per epoch ("Provided that $\varepsilon_\tau \le 1/4(K+2)$", ec3).
--   - reading: "for all $\tau$" → every epoch that is completed within the $T$ periods; reason: the truncated last epoch has fewer than $T_\tau$ samples, and its estimate is never used.
--   - reading: "with probability $1 - O(\tau_0N/T^2)$" → $\exists\, C, T_1$ placed before all other quantifiers, bad-event mass $\le C(\tau_0+1)N/T^2$ for $T \ge T_1$, $\tau_0$ the 0-based index of the last epoch; reason: the stronger of the readings of $O(\cdot)$, with $\tau_0$ counting the epochs (p. 21: "the total number of epochs $\tau_0$"); a bound $C\tau_0N/T^2$ would be $0$ when only epoch $0$ runs and it ends exactly at $T$ ($T_0 = T$, which happens for arbitrarily large $T$), where the bad event has positive probability; for $\tau_0 \ge 1$ the two forms differ by a factor at most $2$.
--   - reading: "argmax" in line 5 → every tie-break satisfying the argmax property; reason: the argmax need not be unique.
--   - generalization: outlier distribution $Q_t$ fixed before $S_t$ is offered → $Q_t$ may depend on the offered assortment; reason: the adversary class only grows, so the bound over all adversaries specializes to the source's.
--   - generalization: $\varepsilon \in [0,1)$ → $\varepsilon \ge 0$; reason: the source's range is included.
--   - encoding: $T_0 = 128(K+1)^2N\ln T$ → $\lceil 128(K+1)^2N\ln T\rceil$, the hypothesis $T_0 \ge 128(K+1)^2N_\tau \ln T$ holds by construction, periods are $0,\dots,T-1$, the probability is a finite sum over records (drawn item, type, purchase), and (A1) is required on every public record; reason: Lean conventions that keep every run of the source's algorithm.
-- source:
--   Chen, Krishnamurthy, Wang, Robust Dynamic Assortment Optimization in the Presence of Outlier Customers, arXiv:1910.04183v2, p. 13, Lemma 1, (7); proof pp. ec1–ec3 (PDF 28–30)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model
import Definitions.Def_OutlierAssort_ActiveElim_Algorithm

namespace OutlierAssort.ActiveElim

/-- Lemma 1 (p. 13), with the unused condition `T_τ ≥ max{ε̄, ε} T / 4(K + 1)` dropped: there are
universal `C` and `T₁` such that, for `T ≥ T₁`, with probability at least `1 − C (τ₀ + 1) N / T²`
(`τ₀ + 1` epochs, `τ₀` the index of the last one) every
completed epoch `τ` with `min{1, ε T / T_τ} ≤ 1 / (4 (K + 2))` has
`|v̂_i^{(τ+1)} − v_i| ≤ ∆*_ε(i, τ + 1)` for every `i ∈ A^{(τ+1)}`. -/
theorem lemma_1 :
    ∃ C T1 : ℝ, ∀ (T N K : ℕ), T1 ≤ (T : ℝ) → 1 ≤ N → 1 ≤ K →
      ∀ (r v : Fin N → ℝ), (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (eps epsBar : ℝ), 0 ≤ eps → 0 ≤ epsBar →
      ∀ (adv : Adversary N), OutlierBudget adv T eps →
      ∀ (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)), IsArgmaxSel r K sel →
        prob (⟨T, epsBar, r, K, sel⟩ : Input N) v adv
            (fun h => ∃ τ : ℕ, epochStart N K T (τ + 1) ≤ T ∧
              min 1 (eps * T / (epochLen N K T τ : ℝ)) ≤ 1 / (4 * ((K : ℝ) + 2)) ∧
              ¬ EstimateWithin (⟨T, epsBar, r, K, sel⟩ : Input N) v eps h τ) ≤
          C * ((tau0 N K T : ℝ) + 1) * N / (T : ℝ) ^ 2 := by sorry

end OutlierAssort.ActiveElim
