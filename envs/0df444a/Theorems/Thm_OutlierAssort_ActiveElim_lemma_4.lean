-- Prove2me | Theorems.Thm_OutlierAssort_ActiveElim_lemma_4
-- name    : OutlierAssort.ActiveElim.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:10.318483+00:00
-- url     : https://prove2.me/theorems/3c779cbe-dd56-4639-aca4-7c01c5aceaa0
-- title:
--   Lemma 4, p. 14 (corrected: line 14 read with min) — on {S* ⊆ A^{(τ)} ∀τ}, w.p. 1 − O(τ₀N/T²), R(S*; v) − R(S_τ^{(i)}; v) ≤ 4∆̂_ε̄(τ) for τ ≤ τ₀, i ∈ A^{(τ+1)}
-- statement:
--   Run Algorithm 1 with horizon $T$, input $\bar\varepsilon$, revenues and utilities in $[0,1]$ and capacity $K \ge 1$, against any adaptive adversary sending at most $\varepsilon T$ outliers, where $0 \le \varepsilon \le \bar\varepsilon$, with any argmax tie-break. Let $S^*$ be any optimal assortment.
--
--   There are universal constants $C$ and $T_1$ such that for $T \ge T_1$ the following event has probability at most $C\tau_0 N/T^2$. The event is that $S^* \subseteq \mathcal A^{(\tau)}$ for every $\tau \le \tau_0+1$, and yet some epoch $\tau \le \tau_0$ and item $i \in \mathcal A^{(\tau+1)}$ have
--   $$
--   R(S^*; v) - R(S^{(i)}_\tau; v) > 4\hat\Delta_{\bar\varepsilon}(\tau).
--   $$
--
--   Every assortment offered in epoch $\tau$ is some $S^{(i)}_\tau$ with $i \in \mathcal A^{(\tau+1)}$, so the lemma bounds the regret of each period of epoch $\tau$ by $4\hat\Delta_{\bar\varepsilon}(\tau)$.
--
--   Differences from the source:
--   - correction: Algorithm 1 line 14 $\max\{1, n_i/n_0(i)\}$ → $\min\{1, n_i/n_0(i)\}$, and $1$ when $n_0(i)=0$; reason: the printed rule contradicts $\hat v \in [0,1]^N$ (p. 9) and the proof (ec3).
--   - reading: "Suppose $S^* \subseteq \mathcal A^{(\tau)}$ holds for all $\tau$. Then with probability $1-O(\tau_0N/T^2)$, …" → the intersection of that event with the failure of the conclusion has probability at most $C\tau_0N/T^2$; reason: the premise is a random event, and the proof (ec5) shows exactly this (the failure lies inside the failure of Lemma 1); with Lemma 3 it also bounds the conditional probability for large $T$.
--   - reading: no hypothesis on $\varepsilon$ → $\varepsilon \le \bar\varepsilon$; reason: the standing assumption of Theorem 1 and Lemma 3, whose proofs this lemma serves; the proof (ec5) applies Corollary 1 at $\max\{\varepsilon,\bar\varepsilon\} = \bar\varepsilon$.
--   - reading: "$S^*$" → every optimal assortment; "for all $\tau$" in the premise → every $\tau \le \tau_0+1$; reason: the argmax defining $S^*$ need not be unique, and these are the active sets the run computes.
--   - reading: "with probability $1 - O(\tau_0N/T^2)$" → $\exists\, C, T_1$ placed before all other quantifiers; reason: the stronger of the readings of $O(\cdot)$.
--   - reading: "argmax" in line 5 → every tie-break satisfying the argmax property; reason: the argmax need not be unique.
--   - generalization: outlier distribution $Q_t$ fixed before $S_t$ is offered → $Q_t$ may depend on the offered assortment; reason: the adversary class only grows.
--   - generalization: $\varepsilon \in [0,1)$ → $\varepsilon \ge 0$; reason: the source's range is included.
--   - encoding: $T_0 = 128(K+1)^2N\ln T$ → $\lceil\cdot\rceil$, periods $0,\dots,T-1$, finite sum over records, (A1) on every public record; reason: Lean conventions that keep every run of the source's algorithm.
-- source:
--   Chen, Krishnamurthy, Wang, Robust Dynamic Assortment Optimization in the Presence of Outlier Customers, arXiv:1910.04183v2, p. 14, Lemma 4; proof p. ec5 (PDF 32)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model
import Definitions.Def_OutlierAssort_ActiveElim_Algorithm

namespace OutlierAssort.ActiveElim

/-- Lemma 4 (p. 14): with probability at least `1 − C τ₀ N / T²`, it does not happen that an optimal
assortment `S*` stays in every active set while some epoch `τ ≤ τ₀` and item `i ∈ A^{(τ+1)}` have
`R(S*; v) − R(S_τ^{(i)}; v) > 4 ∆̂_ε̄(τ)`. -/
theorem lemma_4 :
    ∃ C T1 : ℝ, ∀ (T N K : ℕ), T1 ≤ (T : ℝ) → 1 ≤ N → 1 ≤ K →
      ∀ (r v : Fin N → ℝ), (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (eps epsBar : ℝ), 0 ≤ eps → eps ≤ epsBar →
      ∀ (adv : Adversary N), OutlierBudget adv T eps →
      ∀ (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)), IsArgmaxSel r K sel →
      ∀ (Sstar : Finset (Fin N)), IsOptimal r v K Sstar →
        prob (⟨T, epsBar, r, K, sel⟩ : Input N) v adv
            (fun h =>
              (∀ τ : ℕ, τ ≤ tau0 N K T + 1 →
                Sstar ⊆ (state (⟨T, epsBar, r, K, sel⟩ : Input N) h τ).A) ∧
              ∃ τ : ℕ, τ ≤ tau0 N K T ∧
                ∃ i ∈ (state (⟨T, epsBar, r, K, sel⟩ : Input N) h (τ + 1)).A,
                  4 * (state (⟨T, epsBar, r, K, sel⟩ : Input N) h τ).dhat <
                    rev r v Sstar - rev r v
                      (sel (state (⟨T, epsBar, r, K, sel⟩ : Input N) h τ).vhat
                        (state (⟨T, epsBar, r, K, sel⟩ : Input N) h τ).A i)) ≤
          C * (tau0 N K T : ℝ) * N / (T : ℝ) ^ 2 := by sorry

end OutlierAssort.ActiveElim
