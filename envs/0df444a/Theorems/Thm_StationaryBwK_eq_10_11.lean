-- Prove2me | Theorems.Thm_StationaryBwK_eq_10_11
-- name    : StationaryBwK.eq_10_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:22.288706+00:00
-- url     : https://prove2.me/theorems/278099f2-5bae-4616-8971-aa4ea1bff5b7
-- title:
--   (10)–(11): the $\mathrm{Alg}_{\max}$ side, realized to expected rewards
-- statement:
--   Let $T\ge1$, $0<B\le T$, $\rho=B/T$, and fix one outcome of a run. Let $A\in\Delta([K])$ satisfy $\mathbb E_{a\sim A}[c_{t,i}(a)]\le\rho$ for every round $t\in[T]$ and resource $i$, let $r_t(a)\le1$ for $t\in[T]$, and suppose that for some $\varepsilon$ and every action $a$, $Z_{T_A}(a)-Z_0(a)\ge-\varepsilon$. Then
--   $$\max_{a\in[K]}\sum_{t=1}^{T_A}\mathcal L_t(a,I_t)\ \ge\ \sum_{t=1}^{T}\mathbb E_{a\sim A}[r_t(a)]-(T-T_A)-\varepsilon .$$
--
--   This is the side of the proof of Lemma 5.1 that uses the maximizing subroutine: the best fixed action earns at least the comparator distribution's expected reward over the whole horizon, up to the rounds lost after stopping.
--
--   Differences from the source:
--   - generalization: the random run of Algorithm 1 → one outcome ω of arbitrary sequences R, C, A (and I); reason: the display is a pathwise inequality; the paper applies it at each outcome
--   - reading: the chains (10)–(11) start from Σ_{t≤T_A} L_t(A_t, I_t) + Reg_max(T, δ₂) and use the Azuma event, ending with −Reg_max(T, δ₃) → from max_a Σ_{t≤T_A} L_t(a, I_t), with the Azuma bound at T′ = T_A as a hypothesis with an arbitrary ε; reason: the first step is guarantee (4) at T′ = T_A, a hypothesis of Lemma 5.1; Reg_max(T, δ₃) is the O(·) name of the Azuma term ε
--   - generalization: r_t(a) a conditional expectation in [0, 1] → r_t(a) ≤ 1, otherwise arbitrary; reason: the proof uses only r_t(a) ≤ 1 ('in the last one that r_t(a) ≤ 1')
--   - reading: the game ends after round T or when a resource is depleted; T_A = max{t ∈ [T] : ∀i, Σ_{τ≤t} C_{τ,i}(A_τ) ≤ B} → R, C, A, I are defined on all rounds 1, …, T and only REW is cut at T_A; T_A = 0 when the set is empty; reason: OPT_FD and Definition 3.1 range over all t ∈ [T]; if round 1 already overdraws the player receives no reward
--   - encoding: rounds t ∈ [T], actions [K] with a null action, resources [d], Alg_min's choice i ∈ [d] ∪ {0} → rounds are natural numbers 1, …, T; actions Fin K with a designated null action a₀; resources Fin d; i ∈ Option (Fin d) with none = 0; reason: Lean convention; same instances
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, proof of Lemma 5.1, displays (10) and (11), p.16

import Mathlib
import Definitions.Def_StationaryBwK_Benchmark
import Definitions.Def_StationaryBwK_Play

namespace StationaryBwK

/-- **Displays (10)–(11)** (Fikioris & Tardos, arXiv:2302.14686v2, proof of Lemma 5.1, p.16), the
`Alg_max` side of the proof, at one outcome. Let `T ≥ 1`, `0 < B ≤ T`, `ρ = B/T`, let `A` be a
distribution of actions with `E_{a∼A}[c_{t,i}(a)] ≤ ρ` for every round `t ∈ [T]` and resource `i`,
let `r_t(a) ≤ 1` for `t ∈ [T]`, and suppose the Azuma bound `Z_{T_A}(a) − Z_0(a) ≥ −ε` holds at
`T′ = T_A` for every action `a`. Then
`max_{a∈[K]} Σ_{t=1}^{T_A} L_t(a, I_t) ≥ Σ_{t=1}^{T} E_{a∼A}[r_t(a)] − (T − T_A) − ε`.

**Formalization Note.** `ε` is any real; on p.16 it is `(1 + 1/ρ)√(2T log(TK/δ₃))`, which the
paper then writes as `Reg_max(T, δ₃)`. The term `Reg_max(T, δ₂)` on the left of the printed chain
is guarantee (4) and is not part of this statement. `r`, `c` are arbitrary real functions. -/
theorem eq_10_11 {Ω : Type*} {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (R : ℕ → Ω → Fin K → ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ) (A : ℕ → Ω → Fin K)
    (I : ℕ → Ω → Option (Fin d)) (r : ℕ → Fin K → Ω → ℝ) (c : ℕ → Fin d → Fin K → Ω → ℝ)
    (ω : Ω) (ε : ℝ) (p : Fin K → ℝ) (hp : p ∈ stdSimplex ℝ (Fin K))
    (hpc : ∀ t ∈ Finset.Icc 1 T, ∀ i, expect p (fun a => c t i a ω) ≤ rho T B)
    (hr : ∀ t ∈ Finset.Icc 1 T, ∀ a, r t a ω ≤ 1)
    (hZ : ∀ a : Fin K,
      -ε ≤ zProc (rho T B) R C r c I (stopTime T B C A ω) a ω - zProc (rho T B) R C r c I 0 a ω) :
    ∑ t ∈ Finset.Icc 1 T, expect p (fun a => r t a ω) -
        ((T : ℝ) - (stopTime T B C A ω : ℝ)) - ε ≤
      ⨆ a : Fin K, ∑ t ∈ Finset.Icc 1 (stopTime T B C A ω), lagr (rho T B) R C t ω a (I t ω) := by sorry

end StationaryBwK
