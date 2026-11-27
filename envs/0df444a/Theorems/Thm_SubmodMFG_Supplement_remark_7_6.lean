-- Prove2me | Theorems.Thm_SubmodMFG_Supplement_remark_7_6
-- name    : SubmodMFG.Supplement.remark_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:28:42.464194+00:00
-- url     : https://prove2.me/theorems/cc929c10-3cf8-43fb-8ef8-a4cc150709cd
-- title:
--   Remark 7.6 — the optimal-stopping best responses form a lattice with monotone attained extremes, and $\inf R(m)$, $\sup R(m)$ are attained through $p$
-- statement:
--   In the optimal-stopping MFG of §7, under its standing assumptions and Assumptions 7.2 and 7.4, let $\hat R(m)\subseteq E$ be the stopping times maximizing $J(\cdot,m)$ and $R(m)=p(\hat R(m))\subseteq L$.
--
--   1. $\hat R(m)$ is a lattice: $\tau_1,\tau_2\in\hat R(m)$ imply $\tau_1\wedge\tau_2,\ \tau_1\vee\tau_2\in\hat R(m)$.
--   2. For $m\le\bar m$ in $L$: $\inf_E\hat R(m)\le\inf_E\hat R(\bar m)$ and $\sup_E\hat R(m)\le\sup_E\hat R(\bar m)$.
--   3. For every $m\in L$: $\inf_E\hat R(m)\in\hat R(m)$ and $\sup_E\hat R(m)\in\hat R(m)$.
--   4. (7.9) For every $m\in L$,
--   $$\inf R(m)=p\big(\inf_E\hat R(m)\big)\in R(m),\qquad \sup R(m)=p\big(\sup_E\hat R(m)\big)\in R(m).$$
--
--   These are the conclusions of Lemma 2.4 for the stopping game, obtained without Condition 2 of Assumption 2.1.
--
--   **Formalization Note** Infima and suprema in $E$ are for the a.s. order of stopping times, in $L$ for $\le_L$; (4) is stated for every version of $p(\inf_E\hat R(m))$ lying in $L$, together with the existence of such a version.
--
--   Differences from the source:
--   - reading: (7.7) R̂(m) := arg min_E J(·, m) → R̂(m) = arg max_E J(·, m); reason: J is a profit to be maximized: §7.1 (p.29), Definition 7.1 ('τ^m ∈ arg max'), and the proof of Theorem 7.7 (J(τⁿ, mⁿ⁻¹) ≥ J(τ, mⁿ⁻¹), p.32)
--   - reading: the future-increment σ-field is printed with t ≤ s₁ ≤ s₁ ≤ T → t ≤ s₁ ≤ s₂ ≤ T; reason: the displayed generators are B_{s₂}−B_{s₁}, so the repeated s₁ is a typographical error
--   - encoding: τ₁ ∧ τ₂, τ₁ ∨ τ₂ ∈ R̂(m); inf_E, sup_E → explicit stopping times equal to the pointwise min and max exist and lie in R̂(m); IsGLB/IsLUB for the a.s. preorder; reason: min and max of stopping times are stopping times; the a.s. preorder's antisymmetrization is the paper's lattice E
--   - encoding: inf R(m) = p(inf_E R̂(m)) ∈ R(m) → every version m' ∈ L of p(inf_E R̂(m)) is a greatest lower bound of R(m) and lies in R(m), and such a version exists; reason: p is defined up to versions; R(m) is closed under ≤_L-equivalence
--   - encoding: stopping times τ ≤ T P-a.s.; conditional probabilities P[· | F^B_t] P-a.s.; J(τ, m) = E[…] → τ with values in [0, T] everywhere; identities for each (t, A) a.s. (Mathlib conditional expectation of indicators); J in [0, ∞] with f, g ≥ 0; reason: a null-set modification under the usual conditions; nonnegativity is Assumption 7.2 (2)
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §7.3, Remark 7.6 and (7.9), p.31 ((7.6), (7.7), p.31)

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb
import Definitions.Def_RepairSched_UsualConditions
import Definitions.Def_SubmodMFG_Supplement_Processes
import Definitions.Def_SubmodMFG_Supplement_StoppingMFG

open MeasureTheory

namespace SubmodMFG.Supplement

/-- **Remark 7.6** — the optimal-stopping best responses form a lattice with monotone attained
extremes, and `inf R(m)`, `sup R(m)` are attained through the projection `p`.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §7.3, Remark 7.6, p.31: "… (1) The set R̂(m) is a lattice, i.e. for every
τ₁, τ₂ ∈ R̂(m), one has τ₁ ∧ τ₂, τ₁ ∨ τ₂ ∈ R̂(m); (2) For all m, m̄ ∈ L with m ≤ m̄,
inf_E R̂(m) ≤ inf_E R̂(m̄) and sup_E R̂(m) ≤ sup_E R̂(m̄); (3) For every m ∈ L, inf_E R̂(m) ∈ R̂(m)
and sup_E R̂(m) ∈ R̂(m). Therefore, due to the monotonicity of the projection p (see (7.4)), for
any m ∈ L, we have (7.9) inf R(m) = p(inf_E R̂(m)) ∈ R(m) and sup R(m) = p(sup_E R̂(m)) ∈ R(m)".

**Formalization Note.** Standing assumptions of §7.1 and Assumptions 7.2, 7.4. `R̂(m)` is the set
of maximizers of `J(·, m)` ((7.7) with "arg max", see `StopModel.Rhat`); `τ₁ ∧ τ₂`, `τ₁ ∨ τ₂` are
the pointwise minimum and maximum; `inf_E`, `sup_E` are `IsGLB`/`IsLUB` for the a.s. order of `E`,
and `inf R(m)`, `sup R(m)` are `IsGLB`/`IsLUB` in `L`. (7.9) is stated for every version `m'` of
`p(inf_E R̂(m))` lying in `L`, together with the existence of such a version. -/
theorem remark_7_6 {Ω : Type*} [MeasurableSpace Ω] {d₁ d₂ : ℕ} (M : StopModel Ω d₁ d₂)
    (hM : M.Standing) (h72 : M.Assumption72) (h74 : M.Assumption74) :
    -- (1)
    (∀ m : M.FlowL, ∀ τ₁ ∈ M.Rhat m.1, ∀ τ₂ ∈ M.Rhat m.1,
      (∃ τ : M.StopTime,
        τ.1 = (fun ω => min (τ₁.1 ω) (τ₂.1 ω)) ∧ τ ∈ M.Rhat m.1) ∧
      (∃ τ : M.StopTime,
        τ.1 = (fun ω => max (τ₁.1 ω) (τ₂.1 ω)) ∧ τ ∈ M.Rhat m.1)) ∧
    -- (2)
    (∀ m m' : M.FlowL, m ≤ m' →
      (∀ a b : M.StopTime, IsGLB (M.Rhat m.1) a → IsGLB (M.Rhat m'.1) b → a ≤ b) ∧
      (∀ a b : M.StopTime, IsLUB (M.Rhat m.1) a → IsLUB (M.Rhat m'.1) b → a ≤ b)) ∧
    -- (3)
    (∀ m : M.FlowL,
      (∃ a : M.StopTime, IsGLB (M.Rhat m.1) a ∧ a ∈ M.Rhat m.1) ∧
      (∃ a : M.StopTime, IsLUB (M.Rhat m.1) a ∧ a ∈ M.Rhat m.1)) ∧
    -- (7.9)
    (∀ m : M.FlowL,
      (∀ a : M.StopTime, IsGLB (M.Rhat m.1) a →
        (∃ m' : M.FlowL, M.IsCondProj (fun t => {ω | t < a.1 ω}) m'.1) ∧
        ∀ m' : M.FlowL, M.IsCondProj (fun t => {ω | t < a.1 ω}) m'.1 →
          IsGLB (M.R m) m' ∧ m' ∈ M.R m) ∧
      (∀ a : M.StopTime, IsLUB (M.Rhat m.1) a →
        (∃ m' : M.FlowL, M.IsCondProj (fun t => {ω | t < a.1 ω}) m'.1) ∧
        ∀ m' : M.FlowL, M.IsCondProj (fun t => {ω | t < a.1 ω}) m'.1 →
          IsLUB (M.R m) m' ∧ m' ∈ M.R m)) := by sorry

end SubmodMFG.Supplement
