-- Prove2me | Theorems.Thm_StationaryBwK_azuma_Z
-- name    : StationaryBwK.azuma_Z
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:14.958748+00:00
-- url     : https://prove2.me/theorems/46e3d903-466f-41d2-b4d8-58812444a64f
-- title:
--   Proof of Lemma 5.1, p.16: Azuma–Hoeffding and the union bound for $Z_{T'}(a)$
-- statement:
--   Consider the adaptive BwK model with $T\ge1$ rounds, $K$ actions, $0<B\le T$, $\rho=B/T$, and a player satisfying the no-knowledge condition. For any $\delta_3>0$, with probability at least $1-\delta_3$, for all $T'\in[T]$ and all $a\in[K]$,
--   $$Z_{T'}(a)-Z_0(a)\ \ge\ -\Big(1+\frac1\rho\Big)\sqrt{2T\log(TK/\delta_3)} .$$
--
--   Combined with (10), this turns the realized rewards and consumptions of the comparator distribution into their conditional expectations, uniformly over actions and rounds.
--
--   Differences from the source:
--   - generalization: the run of Algorithm 1 → any player whose choices A_t, I_t are adapted and satisfy the no-knowledge condition; reason: the martingale argument uses no other property of Algorithm 1
--   - generalization: the player chooses A_t (and I_t) without any knowledge of the reward or consumptions of that round or their distribution → conditional mean independence: E[R_t(a) | ℋ_{t−1} ∨ σ(A_t, I_t)] = E[R_t(a) | ℋ_{t−1}] a.s., and the same for C_{t,i}(a); reason: implied by conditional independence of round t's rewards and consumptions from the round-t choices; it is the only form the martingale step on p.16 uses
--   - reading: r_t(a) = E[R_t(a) | H_{t−1}] for the history H_t of actions and realized rewards and consumptions → a filtration ℋ to which R_t, C_t, A_t and I_t are adapted, with r_t(a) = E[R_t(a) | ℋ_{t−1}] and c_{t,i}(a) likewise; reason: the martingale Z on p.16 uses I_t, so Alg_min's choices must be in the history; the paper's H_t enlarged by the player's own choices is an instance
--   - reading: Z_{T′}(a) − Z_0(a) ≥ −(1 + 1/ρ)√(2T log(TK/δ₃)) ≥ −Reg_max(T, δ₃) → the first inequality only; reason: the second is the O(·) absorption into Reg_max, which is defined only up to constants
--   - encoding: with probability at least 1 − δ → there is a measurable event E with μ(E) ≥ 1 − δ on which the inequality holds; reason: avoids the measure of a possibly non-measurable set; same meaning
--   - encoding: rounds t ∈ [T], actions [K] with a null action, resources [d], Alg_min's choice i ∈ [d] ∪ {0} → rounds are natural numbers 1, …, T; actions Fin K with a designated null action a₀; resources Fin d; i ∈ Option (Fin d) with none = 0; reason: Lean convention; same instances
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, proof of Lemma 5.1, p.16 ("we can use the Azuma-Hoeffding inequality and the union bound")

import Mathlib
import Definitions.Def_StationaryBwK_Play
import Definitions.Def_StationaryBwK_Model
import Definitions.Def_StationaryBwK_Regret

open MeasureTheory

namespace StationaryBwK

/-- **Azuma–Hoeffding with a union bound** (Fikioris & Tardos, arXiv:2302.14686v2, proof of
Lemma 5.1, p.16). Against any adaptive adversary and any player satisfying the model of §2 and
Algorithm 1: for any `δ₃ > 0`, with probability at least `1 − δ₃`, for all `T′ ∈ [T]` and all
`a ∈ [K]`, `Z_{T′}(a) − Z_0(a) ≥ −(1 + 1/ρ) √(2T log(TK/δ₃))`.

**Formalization Note.** "With probability at least `1 − δ₃`" is a measurable event of measure at
least `1 − δ₃`. The printed chain continues with `≥ −Reg_max(T, δ₃)`, an `O(·)` absorption that is
not part of this statement. -/
theorem azuma_Z {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℋ : Filtration ℕ m0) {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (a₀ : Fin K) (R : ℕ → Ω → Fin K → ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ)
    (A : ℕ → Ω → Fin K) (I : ℕ → Ω → Option (Fin d))
    (hEnv : IsBwKEnvironment ℋ T a₀ R C) (hPlayer : IsBwKPlayer μ ℋ T R C A I) :
    ∀ δ₃ : ℝ, 0 < δ₃ → ∃ E : Set Ω, MeasurableSet E ∧ 1 - δ₃ ≤ μ.real E ∧
      ∀ ω ∈ E, ∀ T' ∈ Finset.Icc 1 T, ∀ a : Fin K,
        -azumaTerm T K (rho T B) δ₃ ≤
          zProc (rho T B) R C (rCond μ ℋ R) (cCond μ ℋ C) I T' a ω -
            zProc (rho T B) R C (rCond μ ℋ R) (cCond μ ℋ C) I 0 a ω := by sorry

end StationaryBwK
