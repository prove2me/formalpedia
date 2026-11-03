-- Prove2me | Theorems.Thm_StationaryBwK_scaled_distribution_budget
-- name    : StationaryBwK.scaled_distribution_budget
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:34.171436+00:00
-- url     : https://prove2.me/theorems/90c8dab8-8b9e-4761-a567-23e77290e502
-- title:
--   Proof of Theorem 5.2, p.18: playing $A^*$ with probability $\max\{\rho,\sigma_c x\}$ keeps $\mathbb E_{a\sim A}[c_{t,i}(a)]\le\rho$
-- statement:
--   Let $T\ge1$, $0<B\le T$, $\rho=B/T$, $\sigma_c\in[0,1]$. Let the consumptions $c_{t,i}(a)$ lie in $[0,1]$ for $t\in[T]$, vanish at a null action $a_0$, and be $\sigma_c$-stationary. Let $(A^*,T^*)$ be an optimal solution to (1), $x=T^*/T$, and let $A$ play $A^*$ with probability $\max\{\rho,\sigma_c x\}$ and the null action otherwise. Then $A\in\Delta([K])$ and for every resource $i$ and round $t\in[T]$,
--   $$\mathbb E_{a\sim A}[c_{t,i}(a)]\ \le\ \rho .$$
--
--   This makes the scaled optimal distribution an admissible comparator in Lemma 5.1, which is how Theorem 5.2 is derived.
--
--   Differences from the source:
--   - generalization: r_t(a), c_{t,i}(a) the conditional expectations of one realized history, in [0, 1] → arbitrary real sequences r, c; reason: the proof uses only the stated hypotheses; the paper applies it at each outcome, where r, c are such sequences
--   - generalization: a (σr, σc)-stationary adversary (proof of Theorem 5.2, p.18) → only the consumptions are σc-stationary; nothing is assumed about the rewards; reason: the display on p.18 uses only Lemma A.2 and c_{t,i}(a) ≤ 1; every (σr, σc)-stationary instance satisfies the Lean hypotheses
--   - reading: (A*, T*) the optimal solution to (1) → any optimal solution of (1) (feasible, with value at least that of every feasible point); reason: the paper writes 'the' solution; nothing in the proof depends on which optimal solution is chosen
--   - generalization: A is 'the arm distribution that plays A∗ with probability max{ρ, σc x} and otherwise the null arm' → also the conclusion A ∈ Δ([K]); reason: implicit in the page (A is called a distribution); it uses ρ ≤ 1 and σc x ≤ 1
--   - encoding: E_{a∼A}[c_{t,i}(a)] = max{ρ, σc x} E_{a∼A∗}[c_{t,i}(a)] ≤ max{ρ, σc x} min{1, ρ/(σc x)} = ρ → the end-to-end bound E_{a∼A}[c_{t,i}(a)] ≤ ρ, for every σc ∈ [0, 1]; reason: the intermediate expression has a division by σc x, undefined at σc = 0, where the bound still holds with max{ρ, 0} = ρ
--   - encoding: min_t f(t) ≥ σ max_t f(t) over t ∈ [T] (Definition 3.1) → σ f(s) ≤ f(t) for all s, t ∈ [T] (IsStationarySeq); reason: equivalent for a finite nonempty index set
--   - encoding: rounds t ∈ [T], actions [K] with a null action, resources [d], Alg_min's choice i ∈ [d] ∪ {0} → rounds are natural numbers 1, …, T; actions Fin K with a designated null action a₀; resources Fin d; i ∈ Option (Fin d) with none = 0; reason: Lean convention; same instances
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, proof of Theorem 5.2, p.18, first display

import Mathlib
import Definitions.Def_StationaryBwK_Benchmark
import Definitions.Def_StationaryBwK_StationarySeq

namespace StationaryBwK

/-- **The scaled optimal distribution respects the per-round budget** (Fikioris & Tardos,
arXiv:2302.14686v2, proof of Theorem 5.2, p.18, first display). Let `ρ = B/T` with `0 < B ≤ T`,
let the consumptions lie in `[0, 1]`, vanish at the null action `a₀`, and be `σc`-stationary with
`σc ∈ [0, 1]`; let `(A*, T*)` be the optimal solution to (1) and `x = T*/T`. Let `A` play `A*` with
probability `max{ρ, σc x}` and the null action otherwise. Then `A ∈ Δ([K])` and for every resource
`i` and round `t ∈ [T]`, `E_{a∼A}[c_{t,i}(a)] ≤ ρ`.

**Formalization Note.** Deterministic: `r`, `c` are real sequences. The case `σc = 0` is included
(then `max{ρ, σc x} = ρ`); the printed intermediate bound `max{ρ, σc x} min{1, ρ/(σc x)}` is not
stated. -/
theorem scaled_distribution_budget {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B)
    (hBT : B ≤ T) (σc : ℝ) (hσc₀ : 0 ≤ σc) (hσc₁ : σc ≤ 1) (a₀ : Fin K)
    (r : ℕ → Fin K → ℝ) (c : ℕ → Fin d → Fin K → ℝ)
    (hc01 : ∀ t ∈ Finset.Icc 1 T, ∀ i a, c t i a ∈ Set.Icc (0 : ℝ) 1)
    (hc₀ : ∀ t ∈ Finset.Icc 1 T, ∀ i, c t i a₀ = 0)
    (hc : ∀ (i : Fin d) (a : Fin K), IsStationarySeq σc T (fun t => c t i a))
    (Ts : ℕ) (p : Fin K → ℝ) (hopt : IsOptFDSolution T B r c Ts p) :
    mixNull (max (B / T) (σc * ((Ts : ℝ) / T))) p a₀ ∈ stdSimplex ℝ (Fin K) ∧
      ∀ i : Fin d, ∀ t ∈ Finset.Icc 1 T,
        expect (mixNull (max (B / T) (σc * ((Ts : ℝ) / T))) p a₀) (fun a => c t i a) ≤ B / T := by sorry

end StationaryBwK
