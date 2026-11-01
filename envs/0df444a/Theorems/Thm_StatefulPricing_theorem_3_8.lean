-- Prove2me | Theorems.Thm_StatefulPricing_theorem_3_8
-- name    : StatefulPricing.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:27:14.232051+00:00
-- url     : https://prove2.me/theorems/16af7e3e-06ca-447b-bb89-823a04f1bc57
-- title:
--   Theorem 3.8 (corrected: $|\Gamma|\ge2$): C&S has regret $O(\sqrt{\sigma T\log|\Gamma|})$ on $\sigma$-chasable Dd-MDPs
-- statement:
--   For every constant $K_A$ there is a constant $K$ with the following property. Let $M$ be a Dd-MDP instance with rewards in $[0,1]$, $T$ a horizon, $\Gamma$ a finite family of at least two feasible policies and $\sigma>0$. Let $\mathcal A$ be an online OLSC algorithm whose regret with switching cost $\sigma$, horizon $T$ and experts $\Gamma$ is at most $K_A\sqrt{\sigma T\log|\Gamma|}$ against every $[0,1]$-valued reward sequence, and let $\mathcal O$ be a chasing oracle for which $M$ is $\sigma$-chasable for $\Gamma$. Then C&S, run with $\mathcal A$ and $\mathcal O$ (fresh oracle coins for each run), has regret
--   $$
--   \max_{\gamma\in\Gamma}\sum_{t=1}^T f_t\big(s^\gamma(t),x^\gamma(t)\big)-\sum_{t=1}^T\mathbb E\big[f_t(s_t,x_t)\big]\le K\sqrt{\sigma\,T\log|\Gamma|},
--   $$
--   provided its per-round rewards are measurable.
--
--   This is the reduction of online learning on chasable Dd-MDPs to online learning with switching cost.
--
--   Differences from the source:
--   - correction: any $\Gamma$ → $|\Gamma|\ge2$; reason: the proof charges $\sigma$ per switch but the first episode also costs up to $\sigma$: with one state, actions $a,b$, $f_t(s,a)=1$, $f_t(s,b)=0$, $\Gamma=\{\gamma\equiv a\}$, $\sigma=1$ and the oracle playing $b$ in the first round of each run ($\mathrm{CR}\le1=\sigma$), C&S has regret $1>0=O(\sqrt{\sigma T\log1})$; for $|\Gamma|\ge2$ the extra $\sigma$ is absorbed for every $\sigma>0$ ($\sigma\le\sqrt{\sigma T\log|\Gamma|/\log2}$ when $\sigma\le T$, and the regret is at most $T\le\sqrt{\sigma T}$ when $\sigma>T$), so no lower bound on $\sigma$ is needed
--   - reading: C&S with "an algorithm $\mathcal A$ for the OLSC problem" and $O(\sqrt{\sigma T\log|\Gamma|})$ → for every $\mathcal A$ with regret at most $K_A\sqrt{\sigma T\log|\Gamma|}$, the constant $K$ depends only on $K_A$; reason: the proof bounds C&S's regret by $\mathcal A$'s (p.12)
--   - reading: Algorithm 1: invoke the oracle when $t>1$ and $\gamma_t\ne\gamma_{t-1}$, else continue; the oracle is fed rounds $\ge t_{\mathrm{init}}$ → the oracle is also invoked at $t=1$ with $\gamma_1$ and $s_1$, each run gets fresh independent coins, and the oracle sees $s_1$ and $g_s,f_s$ for all $s<t$; reason: the episodes of the proof start at $t=1$; with shared coins a run's initial state would correlate with its own coins; the Theorem 3.4 oracle runs $\gamma$ from round 1
--   - generalization: finite state and action sets → arbitrary state and action types; reason: finiteness is not used, and DRACC's action set is infinite
--   - encoding: expectations $\mathbb E[f_t(s_t,x_t)]$ → the per-round rewards of C&S are assumed measurable; reason: excludes only cases in which the source's expectation is undefined (the field's standing measurability convention)
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, Theorem 3.8, p.11

import Mathlib
import Definitions.Def_StatefulPricing_DdMDP
import Definitions.Def_StatefulPricing_ChasingOracle
import Definitions.Def_StatefulPricing_OLSCAlg
import Definitions.Def_StatefulPricing_candS

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing

/-- **Theorem 3.8** (arXiv:2005.01869v2, p.11): "The regret of C&S for T-round σ-chasable Dd-MDP
instances is O(√(σ · T log |Γ|))."

For every constant `K_A` there is a constant `K` such that: for every Dd-MDP instance with rewards
in `[0,1]`, horizon `T`, finite family `Γ` of at least two feasible policies and `σ > 0`, every
online OLSC algorithm `A` whose regret with switching cost `σ` over `T` rounds and experts `Γ` is
at most `K_A √(σ T log |Γ|)` against every `[0,1]`-valued reward sequence, and every chasing oracle
that is `σ`-chasable for `Γ` on this instance, the regret (Eq. (3)) of C&S run with `A` and the
oracle is at most `K √(σ T log |Γ|)`.

**Formalization Note.** C&S gives each oracle run fresh coins (`csLaw`). The per-round rewards of
C&S are assumed measurable, so that its expected reward is defined. -/
theorem theorem_3_8 :
    ∀ K_A : ℝ, ∃ K : ℝ, ∀ (S X : Type) (M : DdMDP S X), M.RewardsInUnit →
      ∀ (T : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], 2 ≤ Fintype.card ι →
      ∀ Γ : ι → S → X, (∀ j, M.IsPolicy (Γ j)) → ∀ σ : ℝ, 0 < σ →
      ∀ (ΩA : Type) [MeasurableSpace ΩA] (PA : Measure ΩA) [IsProbabilityMeasure PA]
        (A : OLSCAlg ΩA ι), A.IsOnline →
        (∀ F : ℕ → ι → ℝ, (∀ t, 1 ≤ t → t ≤ T → ∀ j, 0 ≤ F t j ∧ F t j ≤ 1) →
          A.regret PA σ T F ≤ K_A * Real.sqrt (σ * T * Real.log (Fintype.card ι))) →
      ∀ (ΩO : Type) [MeasurableSpace ΩO] (PO : Measure ΩO) [IsProbabilityMeasure PO]
        (O : ChasingOracle ΩO S X), O.IsChasable PO M T σ (Set.range Γ) →
        (∀ t, AEMeasurable (fun ω => M.f t ((candS A O Γ).state ω M t) (candS A O Γ ω t M))
          (csLaw PA PO)) →
        (candS A O Γ).regret (csLaw PA PO) M T Γ
          ≤ K * Real.sqrt (σ * T * Real.log (Fintype.card ι)) := by sorry

end StatefulPricing
