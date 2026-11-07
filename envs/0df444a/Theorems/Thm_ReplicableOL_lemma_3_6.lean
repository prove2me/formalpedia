-- Prove2me | Theorems.Thm_ReplicableOL_lemma_3_6
-- name    : ReplicableOL.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:49:22.099434+00:00
-- url     : https://prove2.me/theorems/87ad460f-9e01-405f-9b45-00f93bfdda8c
-- title:
--   Lemma 3.6 — assembly
-- statement:
--   Let $c,\varepsilon,\delta,\nu\in(0,1)$ with $c+\varepsilon<1$, and let $B_\delta$ be the bound of Theorem 2(iv). In the regime $k\ge100$, $\Delta\sqrt L\ge100$, if $B_\delta(\rho/\nu)\le\varepsilon A$, then every learner that is $\rho$-replicable under each law $P_\theta$ of Construction C satisfies, with $\|\widetilde W\|_4$ the seed-uniform bound of Lemma 3.4(c),
--   $$
--   \mathbb P_{\theta,S,R}[\mathrm{Reg}_T\ge cA]\ge\Big(\frac{(1-c-\varepsilon)A}{\|\widetilde W\|_4}\Big)^{4/3}-\rho-\delta-\nu\ge0.1994(1-c-\varepsilon)^{4/3}-\rho-\delta-\nu.
--   $$
--   This assembles the regret identity, the moment bounds and Theorem 2; replicability enters once, through Markov's inequality over seeds.
--
--   Differences from the source:
--   - encoding: $\|\widetilde W\|_4$, "the seed-uniform bound of Lemma 3.4(c)" → the number `wBound (T / L) L Δ`; reason: the page's own reading of the symbol
--   - encoding: a probability bounded below by a real number that may be negative → `ENNReal.ofReal` of that real; reason: when it is negative, both forms say nothing
--   - encoding: a learner whose maps $a_t$ read $[0,1]$-valued losses → `Learner` with maps on all real loss vectors (`Fin t → Fin 2 → ℝ`); reason: a learner on $[0,1]$ extends measurably to $\mathbb R$ and a `Learner` restricts to $[0,1]$; every law and every `embed` sequence here is carried by $[0,1]^2$
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 3.6, p.13

import Mathlib
import Definitions.Def_ReplicableOL_Learner
import Definitions.Def_ReplicableOL_IsReplicableUnder
import Definitions.Def_ReplicableOL_priorBox
import Definitions.Def_ReplicableOL_lawP
import Definitions.Def_ReplicableOL_advantage
import Definitions.Def_ReplicableOL_regretProb
import Definitions.Def_ReplicableOL_Bdelta
import Definitions.Def_ReplicableOL_wBound
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma 3.6.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 3.6, p.13. Both inequalities.

**Formalization Note.** The middle term's `‖W̃‖₄` is the seed-uniform number `wBound`, as the lemma says. The middle quantity is real; the first inequality passes through `ENNReal.ofReal`, the second is a real inequality. The regime is `T / L ≥ 100`, `Δ√L ≥ 100`. -/
theorem lemma_3_6 {R : Type*} [MeasurableSpace R] (PR : Measure R) [IsProbabilityMeasure PR]
    {ρ Δ c ε δ ν : ℝ} {T L : ℕ} (hρ : 0 < ρ) (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4)
    (hk : 100 ≤ T / L) (hreg : 100 ≤ Δ * √(L : ℝ))
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hν : ν ∈ Set.Ioo (0 : ℝ) 1) (hsum : c + ε < 1)
    (hB : Bdelta Δ L δ (ρ / ν) ≤ ε * advantage T L Δ)
    (𝓛 : Learner 2 T R)
    (hrep : ∀ θ ∈ priorBox (T / L) Δ, IsReplicableUnder 𝓛 PR ρ (lawP T L θ)) :
    ENNReal.ofReal (((1 - c - ε) * advantage T L Δ / wBound (T / L) L Δ) ^ (4 / 3 : ℝ) - ρ - δ - ν) ≤
      regretProb 𝓛 PR L Δ (c * advantage T L Δ) ∧
    0.1994 * (1 - c - ε) ^ (4 / 3 : ℝ) - ρ - δ - ν ≤
      ((1 - c - ε) * advantage T L Δ / wBound (T / L) L Δ) ^ (4 / 3 : ℝ) - ρ - δ - ν := by sorry

end ReplicableOL
