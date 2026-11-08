-- Prove2me | Theorems.Thm_StationaryBwK_lemma_A_2
-- name    : StationaryBwK.lemma_A_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:51:24.665395+00:00
-- url     : https://prove2.me/theorems/7c5ec3c1-1b8d-423c-888c-9beb10d1f500
-- title:
--   Lemma A.2: $\max_t\mathbb E_{a\sim A^*}[c_{t,i}(a)]\le\rho/(x\sigma_c)$
-- statement:
--   Let $T\ge1$, $0<B\le T$, $\rho=B/T$, $\sigma_c\in(0,1]$, and let the consumptions be $\sigma_c$-stationary: $\min_{t\in[T]}c_{t,i}(a)\ge\sigma_c\max_{t\in[T]}c_{t,i}(a)$ for every resource $i$ and action $a$. Let $(A^*,T^*)$ be an optimal solution to (1) and $x=T^*/T$. Then for all $i\in[d]$,
--   $$\max_{t\in[T]}\mathbb E_{a\sim A^*}[c_{t,i}(a)]\ \le\ \frac{\rho}{x\sigma_c}.$$
--
--   The optimal distribution never consumes much more per round than its average up to $T^*$; scaled down, it becomes a comparator for Lemma 5.1.
--
--   Differences from the source:
--   - generalization: r_t(a), c_{t,i}(a) the conditional expectations of one realized history, in [0, 1] → arbitrary real sequences r, c; reason: the proof uses only the stated hypotheses; the paper applies it at each outcome, where r, c are such sequences
--   - generalization: a (σr, σc)-stationary adversary (Appendix A, p.17: the two lemmas 'show the effects of a (σr, σc)-stationary adversary') → only the consumptions are σc-stationary; nothing is assumed about the rewards; reason: the proof on p.18 uses only σc-stationarity of c; every (σr, σc)-stationary instance satisfies the Lean hypotheses
--   - reading: (A*, T*) the optimal solution to (1) → any optimal solution of (1) (feasible, with value at least that of every feasible point); reason: the paper writes 'the' solution; nothing in the proof depends on which optimal solution is chosen
--   - encoding: σc ∈ [0, 1] → 0 < σc ≤ 1; reason: ρ/(xσc) is undefined at σc = 0 (Lean would read ρ/0 as 0); the excluded case is one where the printed bound has no value
--   - encoding: max_t E_{a∼A*}[c_{t,i}(a)] ≤ ρ/(xσc) → E_{a∼A*}[c_{t,i}(a)] ≤ ρ/(xσc) for every t ∈ [T]; reason: a bound on the maximum over a finite set is a bound on every element
--   - encoding: min_t f(t) ≥ σ max_t f(t) over t ∈ [T] (Definition 3.1) → σ f(s) ≤ f(t) for all s, t ∈ [T] (IsStationarySeq); reason: equivalent for a finite nonempty index set
--   - encoding: rounds t ∈ [T], actions [K] with a null action, resources [d], Alg_min's choice i ∈ [d] ∪ {0} → rounds are natural numbers 1, …, T; actions Fin K with a designated null action a₀; resources Fin d; i ∈ Option (Fin d) with none = 0; reason: Lean convention; same instances
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, Appendix A, Lemma A.2, p.17; proof p.18

import Mathlib
import Definitions.Def_StationaryBwK_Benchmark
import Definitions.Def_StationaryBwK_StationarySeq

namespace StationaryBwK

/-- **Lemma A.2** (Fikioris & Tardos, arXiv:2302.14686v2, Lemma A.2, p.17; proof p.18). Let the
consumptions be `σc`-stationary (Definition 3.1) with `σc > 0`, let `(A*, T*)` be the optimal
solution to (1) and let `x = T*/T`. Then for all `i ∈ [d]`,
`max_t E_{a∼A*}[c_{t,i}(a)] ≤ ρ/(x σc)`, where `ρ = B/T` and `t` ranges over `[T]`.

**Formalization Note.** Deterministic: `r`, `c` are real sequences. `σc > 0` is needed for
`ρ/(xσc)` to be defined (Lean would read `ρ/0` as `0`). The maximum over `t` is written as a bound
for every `t ∈ [T]`. -/
theorem lemma_A_2 {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (σc : ℝ) (hσc₀ : 0 < σc) (hσc₁ : σc ≤ 1) (r : ℕ → Fin K → ℝ) (c : ℕ → Fin d → Fin K → ℝ)
    (hc : ∀ (i : Fin d) (a : Fin K), IsStationarySeq σc T (fun t => c t i a))
    (Ts : ℕ) (p : Fin K → ℝ) (hopt : IsOptFDSolution T B r c Ts p) :
    ∀ i : Fin d, ∀ t ∈ Finset.Icc 1 T,
      expect p (fun a => c t i a) ≤ B / T / ((Ts : ℝ) / T * σc) := by sorry

end StationaryBwK
