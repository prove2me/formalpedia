-- Prove2me | Theorems.Thm_StationaryBwK_lemma_A_1
-- name    : StationaryBwK.lemma_A_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:51:12.183141+00:00
-- url     : https://prove2.me/theorems/b52eeae1-967c-49bb-9887-68024c430f20
-- title:
--   Lemma A.1: $\sum_{t=T^*+1}^{T}\mathbb E_{a\sim A^*}[r_t(a)]\ge\sigma_r\frac{1-x}{x}\mathrm{OPT}_{FD}$
-- statement:
--   Let $T\ge1$, $0<B\le T$, $\sigma_r\in[0,1]$, and let the rewards be $\sigma_r$-stationary: $\min_{t\in[T]}r_t(a)\ge\sigma_r\max_{t\in[T]}r_t(a)$ for every action $a$. Let $(A^*,T^*)$ be an optimal solution to (1) and $x=T^*/T$. Then
--   $$\sum_{t=T^*+1}^{T}\mathbb E_{a\sim A^*}[r_t(a)]\ \ge\ \sigma_r\,\frac{1-x}{x}\,\mathrm{OPT}_{FD}.$$
--
--   The optimal distribution keeps earning after its own stopping time $T^*$; this bound is what makes stopping early cheap for the algorithm in Theorem 5.2.
--
--   Differences from the source:
--   - generalization: r_t(a), c_{t,i}(a) the conditional expectations of one realized history, in [0, 1] → arbitrary real sequences r, c; reason: the proof uses only the stated hypotheses; the paper applies it at each outcome, where r, c are such sequences
--   - generalization: a (σr, σc)-stationary adversary (Appendix A, p.17: the two lemmas 'show the effects of a (σr, σc)-stationary adversary') → only the rewards are σr-stationary; nothing is assumed about the consumptions beyond (1); reason: the proof on p.17 uses only σr-stationarity of r; every (σr, σc)-stationary instance satisfies the Lean hypotheses
--   - reading: (A*, T*) the optimal solution to (1) → any optimal solution of (1) (feasible, with value at least that of every feasible point); reason: the paper writes 'the' solution; nothing in the proof depends on which optimal solution is chosen
--   - encoding: min_t f(t) ≥ σ max_t f(t) over t ∈ [T] (Definition 3.1) → σ f(s) ≤ f(t) for all s, t ∈ [T] (IsStationarySeq); reason: equivalent for a finite nonempty index set
--   - encoding: OPT_FD = max over T* ∈ [T], A* ∈ Δ([K]) in (1) → the supremum (sSup) of the feasible values, which is attained (optFD_attained); reason: Lean convention; equal to the maximum whenever it exists
--   - encoding: rounds t ∈ [T], actions [K] with a null action, resources [d], Alg_min's choice i ∈ [d] ∪ {0} → rounds are natural numbers 1, …, T; actions Fin K with a designated null action a₀; resources Fin d; i ∈ Option (Fin d) with none = 0; reason: Lean convention; same instances
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, Appendix A, Lemma A.1, p.17

import Mathlib
import Definitions.Def_StationaryBwK_Benchmark
import Definitions.Def_StationaryBwK_StationarySeq

namespace StationaryBwK

/-- **Lemma A.1** (Fikioris & Tardos, arXiv:2302.14686v2, Lemma A.1, p.17). Let the rewards be
`σr`-stationary (Definition 3.1), let `(A*, T*)` be the optimal solution to (1) and let
`x = T*/T`. Then `Σ_{t=T*+1}^{T} E_{a∼A*}[r_t(a)] ≥ σr ((1 − x)/x) OPT_FD`.

**Formalization Note.** Deterministic: `r`, `c` are real sequences (the paper applies the lemma at
each realized history). `T* ≥ 1` (it ranges over `[T]`), so `x > 0`. -/
theorem lemma_A_1 {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (σr : ℝ) (hσr₀ : 0 ≤ σr) (hσr₁ : σr ≤ 1) (r : ℕ → Fin K → ℝ) (c : ℕ → Fin d → Fin K → ℝ)
    (hr : ∀ a : Fin K, IsStationarySeq σr T (fun t => r t a))
    (Ts : ℕ) (p : Fin K → ℝ) (hopt : IsOptFDSolution T B r c Ts p) :
    σr * ((1 - (Ts : ℝ) / T) / ((Ts : ℝ) / T)) * optFD T B r c ≤
      ∑ t ∈ Finset.Icc (Ts + 1) T, expect p (r t) := by sorry

end StationaryBwK
