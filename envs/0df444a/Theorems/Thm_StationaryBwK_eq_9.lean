-- Prove2me | Theorems.Thm_StationaryBwK_eq_9
-- name    : StationaryBwK.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:12.697147+00:00
-- url     : https://prove2.me/theorems/c5e1560f-a324-4de2-8bc0-517c865ba988
-- title:
--   (9): $\min_i\sum_{t\le T_A}\mathcal L_t(A_t,i)\le\mathrm{REW}-(T-T_A)+1/\rho$
-- statement:
--   Let $T\ge1$, $0<B\le T$, $\rho=B/T$, and consider one outcome of a run in which every consumption $C_{t,i}(a)$ with $t\in[T]$ lies in $[0,1]$. With $T_A$ the stopping round and $\mathrm{REW}=\sum_{t=1}^{T_A}R_t(A_t)$,
--   $$\min_{i\in[d]\cup\{0\}}\sum_{t=1}^{T_A}\mathcal L_t(A_t,i)=\sum_{t=1}^{T_A}R_t(A_t)+\min_{i\in[d]\cup\{0\}}\Big\{\frac{\mathbb 1[i>0]}{\rho}\sum_{t=1}^{T_A}(\rho-C_{t,i}(A_t))\Big\}\le\mathrm{REW}-(T-T_A)+\frac1\rho .$$
--
--   This is the side of the proof of Lemma 5.1 that uses the minimizing subroutine: running out of budget early makes some resource's Lagrangian term small.
--
--   Differences from the source:
--   - generalization: the random run of Algorithm 1 → one outcome ω of arbitrary sequences R, C, A (and I); reason: the display is a pathwise inequality; the paper applies it at each outcome
--   - reading: display (9) begins with Σ_{t≤T_A} L_t(A_t, I_t) − Reg_min(T, δ₁) ≤ min_i Σ_{t≤T_A} L_t(A_t, i), with probability at least 1 − δ₁ → the equality and the last inequality of (9), at every outcome; reason: the first step is guarantee (5) at T′ = T_A, a hypothesis of Lemma 5.1, not a consequence; the rest of (9) is the deterministic case analysis
--   - reading: the game ends after round T or when a resource is depleted; T_A = max{t ∈ [T] : ∀i, Σ_{τ≤t} C_{τ,i}(A_τ) ≤ B} → R, C, A, I are defined on all rounds 1, …, T and only REW is cut at T_A; T_A = 0 when the set is empty; reason: OPT_FD and Definition 3.1 range over all t ∈ [T]; if round 1 already overdraws the player receives no reward
--   - encoding: rounds t ∈ [T], actions [K] with a null action, resources [d], Alg_min's choice i ∈ [d] ∪ {0} → rounds are natural numbers 1, …, T; actions Fin K with a designated null action a₀; resources Fin d; i ∈ Option (Fin d) with none = 0; reason: Lean convention; same instances
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, proof of Lemma 5.1, display (9), p.15, and the case analysis following it

import Mathlib
import Definitions.Def_StationaryBwK_Play

namespace StationaryBwK

/-- **Display (9)** (Fikioris & Tardos, arXiv:2302.14686v2, proof of Lemma 5.1, (9), p.15), the
`Alg_min` side of the proof, at one outcome. For `T ≥ 1`, `0 < B ≤ T`, `ρ = B/T`, and
consumptions in `[0, 1]` in every round `t ∈ [T]`,
`min_{i∈[d]∪{0}} Σ_{t=1}^{T_A} L_t(A_t, i)
   = Σ_{t=1}^{T_A} R_t(A_t) + min_{i∈[d]∪{0}} {(1[i>0]/ρ) Σ_{t=1}^{T_A} (ρ − C_{t,i}(A_t))}
   ≤ REW − (T − T_A) + 1/ρ`.

**Formalization Note.** The first line of (9) on p.15, which is guarantee (5) at `T′ = T_A`, is not
part of this statement. `none` is the paper's `i = 0`. Rewards are arbitrary reals. -/
theorem eq_9 {Ω : Type*} {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (R : ℕ → Ω → Fin K → ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ) (A : ℕ → Ω → Fin K) (ω : Ω)
    (hC : ∀ t ∈ Finset.Icc 1 T, ∀ i a, C t ω i a ∈ Set.Icc (0 : ℝ) 1) :
    (⨅ j : Option (Fin d),
        ∑ t ∈ Finset.Icc 1 (stopTime T B C A ω), lagr (rho T B) R C t ω (A t ω) j) =
      ∑ t ∈ Finset.Icc 1 (stopTime T B C A ω), R t ω (A t ω) +
        ⨅ j : Option (Fin d),
          ∑ t ∈ Finset.Icc 1 (stopTime T B C A ω), penalty (rho T B) C t ω (A t ω) j ∧
    (⨅ j : Option (Fin d),
        ∑ t ∈ Finset.Icc 1 (stopTime T B C A ω), lagr (rho T B) R C t ω (A t ω) j) ≤
      rew T B R C A ω - ((T : ℝ) - (stopTime T B C A ω : ℝ)) + 1 / rho T B := by sorry

end StationaryBwK
