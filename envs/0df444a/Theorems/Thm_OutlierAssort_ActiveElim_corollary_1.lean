-- Prove2me | Theorems.Thm_OutlierAssort_ActiveElim_corollary_1
-- name    : OutlierAssort.ActiveElim.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:02.684041+00:00
-- url     : https://prove2.me/theorems/c9897062-808e-48ef-87c4-05143edc1efe
-- title:
--   Corollary 1, p. 14 (corrected: factor max{1, √(K+1)/2} on the last term of ∆̂; second inequality bounds |R − R| by ∆̂_{max{ε,ε̄}}; line 14 read with min)
-- statement:
--   Consider any record of a run of Algorithm 1 with capacity $K \ge 1$, revenues and utilities in $[0,1]$, true outlier proportion $\varepsilon \ge 0$, input $\bar\varepsilon \ge 0$ and any argmax tie-break. For an outlier proportion $e$, let $\tilde\Delta_e(\tau)$ be the **corrected error bound**, defined as follows:
--
--   - $\tilde\Delta_e(0) = 1$;
--   - for $\tau = \sigma+1$ and $T_\sigma < eT/(4(K+1))$, $\tilde\Delta_e(\tau) = 1$;
--   - otherwise
--   $$
--   \tilde\Delta_e(\sigma+1) = 16K(K+1)\Big(\frac{e_\sigma}{2} + \sqrt{\frac{e_\sigma N_\sigma \ln T}{T_\sigma}} + \frac{2N_\sigma\ln T}{3T_\sigma}\Big) + \max\Big\{1, \frac{\sqrt{K+1}}{2}\Big\}\cdot 16\sqrt{\frac{K N_\sigma \ln T}{T_\sigma}},
--   $$
--   with $e_\sigma = \min\{1, eT/T_\sigma\}$ and $N_\sigma = |\mathcal A^{(\sigma+1)}|$.
--
--   Suppose the success events of Lemma 1 hold on the epochs before $\tau$: for every $\sigma < \tau$ with $\min\{1,\varepsilon T/T_\sigma\} \le 1/(4(K+2))$ and every $i \in \mathcal A^{(\sigma+1)}$, $|\hat v^{(\sigma+1)}_i - v_i| \le \Delta^*_\varepsilon(i,\sigma+1)$. Then for every $S \subseteq \mathcal A^{(\tau)}$ with $|S| \le K$,
--   $$
--   \big|R(S;\hat v^{(\tau)}) - R(S;v)\big| \le \tilde\Delta_\varepsilon(\tau) \quad\text{and}\quad \big|R(S;\hat v^{(\tau)}) - R(S;v)\big| \le \tilde\Delta_{\max\{\varepsilon,\bar\varepsilon\}}(\tau).
--   $$
--
--   The corollary makes the algorithm's computed bounds valid confidence widths for the revenue of every candidate assortment. Lemmas 3 and 4 apply it.
--
--   Differences from the source:
--   - correction: last term $16\sqrt{KN_{\tau-1}\ln T/T_{\tau-1}}$ of $\hat\Delta$ → multiplied by $\max\{1,\sqrt{K+1}/2\}$; reason: the printed bound is false for large $K$; at $\tau = 1$, $\varepsilon=\bar\varepsilon=0$, $K=1000$, with $K-1$ items $(r,v)=(1,1)$, $K$ items $(1-\delta, 1/K)$ and a record on which every light item has $\hat v_i = v_i + \Delta^*(i,1)$, the set of light items has error $0.1361 > \hat\Delta(1) = 0.1279$; the proof (ec4) replaces $V_{S^{(i)}}$ inside $\Delta^*$ by $V_S$.
--   - correction: $\hat\Delta_\varepsilon(\tau) \le \hat\Delta_{\max\{\varepsilon,\bar\varepsilon\}}(\tau)$ → $|R(S;\hat v^{(\tau)}) - R(S;v)| \le \tilde\Delta_{\max\{\varepsilon,\bar\varepsilon\}}(\tau)$; reason: $\hat\Delta$ is not monotone in its parameter because of the branch at $T_\sigma < eT/(4(K+1))$; with $K=N=1$, $T=10^{12}$, $\varepsilon = T_0/(12T)$ (so $\varepsilon_0 = 1/(4(K+2))$) and $\bar\varepsilon = 1$, $\hat\Delta_\varepsilon(1) = 2.49 > 1 = \hat\Delta_{\bar\varepsilon}(1)$; the bound on $|R-R|$ is what Lemmas 3 and 4 use.
--   - correction: Algorithm 1 line 14 $\max\{1, n_i/n_0(i)\}$ → $\min\{1, n_i/n_0(i)\}$, and $1$ when $n_0(i)=0$; reason: the printed rule contradicts $\hat v \in [0,1]^N$ (p. 9) and the proof (ec3).
--   - reading: "conditioned on the success events of Lemma 1 on epochs up to $\tau$" → deterministic statement on every record on which those events hold for every $\sigma < \tau$; reason: the corollary is an implication between events.
--   - reading: "argmax" in line 5 → every tie-break satisfying the argmax property; reason: the argmax need not be unique.
--   - generalization: the record of a run → any record of any length; reason: the conclusion is deterministic and the source's records are included.
-- source:
--   Chen, Krishnamurthy, Wang, Robust Dynamic Assortment Optimization in the Presence of Outlier Customers, arXiv:1910.04183v2, p. 14, Corollary 1; proof p. ec4 (PDF 31)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model
import Definitions.Def_OutlierAssort_ActiveElim_Algorithm

namespace OutlierAssort.ActiveElim

/-- Corollary 1 (p. 14), corrected: on every record on which the success events of Lemma 1 hold for
the epochs before `τ`, every `S ⊆ A^{(τ)}` with `|S| ≤ K` has `|R(S; v̂^{(τ)}) − R(S; v)|` at most
the corrected bound `∆̂_ε(τ)` and at most the corrected bound `∆̂_{max{ε, ε̄}}(τ)`. -/
theorem corollary_1 {N : ℕ} (T K : ℕ) (hN : 1 ≤ N) (hK : 1 ≤ K) (r v : Fin N → ℝ)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1)
    (eps epsBar : ℝ) (heps : 0 ≤ eps) (hepsBar : 0 ≤ epsBar)
    (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)) (hsel : IsArgmaxSel r K sel)
    {t : ℕ} (p : Fin t → Rec N) (τ : ℕ)
    (hsucc : ∀ σ < τ, min 1 (eps * T / (epochLen N K T σ : ℝ)) ≤ 1 / (4 * ((K : ℝ) + 2)) →
      EstimateWithin (⟨T, epsBar, r, K, sel⟩ : Input N) v eps p σ)
    (S : Finset (Fin N)) (hS : S ⊆ (state (⟨T, epsBar, r, K, sel⟩ : Input N) p τ).A)
    (hSK : S.card ≤ K) :
    |rev r (state (⟨T, epsBar, r, K, sel⟩ : Input N) p τ).vhat S - rev r v S| ≤
        deltaHatCorAt (⟨T, epsBar, r, K, sel⟩ : Input N) p eps τ ∧
      |rev r (state (⟨T, epsBar, r, K, sel⟩ : Input N) p τ).vhat S - rev r v S| ≤
        deltaHatCorAt (⟨T, epsBar, r, K, sel⟩ : Input N) p (max eps epsBar) τ := by sorry

end OutlierAssort.ActiveElim
