-- Prove2me | Theorems.Thm_StationaryBwK_martingale_Z
-- name    : StationaryBwK.martingale_Z
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:14.280363+00:00
-- url     : https://prove2.me/theorems/7975e6a3-de61-46ed-99f3-9b381bf069a7
-- title:
--   Proof of Lemma 5.1, p.16: $Z_\tau(a)$ is a martingale with increments at most $1+1/\rho$
-- statement:
--   Consider the adaptive BwK model with $T\ge1$ rounds, $0<B\le T$, $\rho=B/T$, and a player satisfying the no-knowledge condition. For every action $a$, the process
--   $$Z_\tau(a)=\sum_{t=1}^{\tau}(R_t(a)-r_t(a))+\sum_{t=1}^{\tau}\frac{\mathbb 1[I_t>0]}{\rho}\big(c_{t,I_t}(a)-C_{t,I_t}(a)\big),\qquad\tau\in\{0\}\cup[T],$$
--   is a martingale with respect to the history $(\mathcal H_\tau)$, and almost surely
--   $$|Z_\tau(a)-Z_{\tau-1}(a)|\le1+\frac1\rho\qquad(\tau\in[T]).$$
--
--   This is the input to the Azuma–Hoeffding step that replaces realized rewards and consumptions by their conditional expectations in the proof of Lemma 5.1.
--
--   **Formalization Note** The process is indexed by $\mathbb N$ and stopped at $T$, so it is constant after round $T$.
--
--   Differences from the source:
--   - generalization: the run of Algorithm 1 → any player whose choices A_t, I_t are adapted and satisfy the no-knowledge condition; reason: the martingale argument uses no other property of Algorithm 1
--   - generalization: the player chooses A_t (and I_t) without any knowledge of the reward or consumptions of that round or their distribution → conditional mean independence: E[R_t(a) | ℋ_{t−1} ∨ σ(A_t, I_t)] = E[R_t(a) | ℋ_{t−1}] a.s., and the same for C_{t,i}(a); reason: implied by conditional independence of round t's rewards and consumptions from the round-t choices; it is the only form the martingale step on p.16 uses
--   - reading: r_t(a) = E[R_t(a) | H_{t−1}] for the history H_t of actions and realized rewards and consumptions → a filtration ℋ to which R_t, C_t, A_t and I_t are adapted, with r_t(a) = E[R_t(a) | ℋ_{t−1}] and c_{t,i}(a) likewise; reason: the martingale Z on p.16 uses I_t, so Alg_min's choices must be in the history; the paper's H_t enlarged by the player's own choices is an instance
--   - encoding: Z_τ(a) for τ ∈ {0} ∪ [T] → the ℕ-indexed process Z_{min(τ,T)}(a); reason: Mathlib martingales are indexed by ℕ; the two agree on {0, …, T}
--   - encoding: C_{t,I_t}(A) in the definition of Z_τ(a) → C_{t,I_t}(a); reason: typo: the display that follows uses C_{τ,I_τ}(a), and the argument needs the same action a throughout
--   - encoding: |Z_τ(a) − Z_{τ−1}(a)| ≤ 1 + 1/ρ → almost surely; reason: r and c are conditional expectations, in [0, 1] only up to null sets
--   - encoding: rounds t ∈ [T], actions [K] with a null action, resources [d], Alg_min's choice i ∈ [d] ∪ {0} → rounds are natural numbers 1, …, T; actions Fin K with a designated null action a₀; resources Fin d; i ∈ Option (Fin d) with none = 0; reason: Lean convention; same instances
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, proof of Lemma 5.1, p.16 (definition of Z_τ(a), "We notice that for every a, Z_τ(a) is a martingale", and "|Z_τ(a) − Z_{τ−1}(a)| ≤ 1 + 1/ρ")

import Mathlib
import Definitions.Def_StationaryBwK_Play
import Definitions.Def_StationaryBwK_Model

open MeasureTheory

namespace StationaryBwK

/-- **`Z_τ(a)` is a martingale with bounded increments** (Fikioris & Tardos, arXiv:2302.14686v2,
proof of Lemma 5.1, p.16: "We notice that for every `a`, `Z_τ(a)` is a martingale" and
"`|Z_τ(a) − Z_{τ−1}(a)| ≤ 1 + 1/ρ`"). Against any adaptive adversary and any player satisfying the
model of §2 and Algorithm 1, for every action `a`, the process
`Z_τ(a) = Σ_{t=1}^{τ} (R_t(a) − r_t(a)) + Σ_{t=1}^{τ} (1[I_t > 0]/ρ) (c_{t,I_t}(a) − C_{t,I_t}(a))`,
`τ ∈ {0} ∪ [T]`, is a martingale with respect to the history, and almost surely
`|Z_τ(a) − Z_{τ−1}(a)| ≤ 1 + 1/ρ` for `τ ∈ [T]`.

**Formalization Note.** The process is indexed by `ℕ` and stopped at `T` (`Z_{min(τ,T)}(a)`), so
it is constant after round `T`. The printed `C_{t,I_t}(A)` is read as `C_{t,I_t}(a)`. The
martingale property uses the player's no-knowledge condition (`IsBwKPlayer`). -/
theorem martingale_Z {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℋ : Filtration ℕ m0) {d K : ℕ} (T : ℕ) (B : ℝ) (hT : 1 ≤ T) (hB : 0 < B) (hBT : B ≤ T)
    (a₀ : Fin K) (R : ℕ → Ω → Fin K → ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ)
    (A : ℕ → Ω → Fin K) (I : ℕ → Ω → Option (Fin d))
    (hEnv : IsBwKEnvironment ℋ T a₀ R C) (hPlayer : IsBwKPlayer μ ℋ T R C A I) (a : Fin K) :
    Martingale
        (fun τ ω => zProc (rho T B) R C (rCond μ ℋ R) (cCond μ ℋ C) I (min τ T) a ω) ℋ μ ∧
      ∀ τ ∈ Finset.Icc 1 T, ∀ᵐ ω ∂μ,
        |zProc (rho T B) R C (rCond μ ℋ R) (cCond μ ℋ C) I τ a ω -
            zProc (rho T B) R C (rCond μ ℋ R) (cCond μ ℋ C) I (τ - 1) a ω| ≤ 1 + 1 / rho T B := by sorry

end StationaryBwK
