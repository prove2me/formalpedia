-- Prove2me | Theorems.Thm_SubmodMFG_Supplement_theorem_7_7
-- name    : SubmodMFG.Supplement.theorem_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:29:10.708268+00:00
-- url     : https://prove2.me/theorems/8393af08-e1be-540a-96e7-5a4225480575
-- title:
--   Theorem 7.7 (companion theorem) — MFG of optimal stopping with common noise: least and greatest equilibria exist, and the lower learning procedure increases to the least one
-- statement:
--   In the optimal-stopping MFG of §7 (profit $J(\tau,m)=E[\int_0^\tau f(t,X_t,m_t)dt+g(\tau,X_\tau)]$ maximized over stopping times $\tau\le T$, equilibria $m_t(A)=P[\psi(X_t)\in A,\ t<\tau^m\mid\mathcal F^B_t]$ of Definition 7.1), under its standing assumptions and Assumptions 7.2 and 7.4:
--
--   1. The set $M$ of MFG equilibria is nonempty, and $\inf M\in M$, $\sup M\in M$ (infimum and supremum in $L$).
--   2. If $f$ is continuous in $m$, then the learning procedure $m^0=\inf L$, $m^{n+1}=\inf R(m^n)$ is nondecreasing in $L$, a least equilibrium $\underline m$ exists, and
--   $$m^n_t\longrightarrow\underline m_t\quad\text{weakly, for }P\otimes dt\text{-a.e. }(\omega,t)\in\Omega\times[0,T].$$
--
--   No convergence is claimed for the upper procedure from $\sup L$ (Remark 7.8): $\mathbf 1\{t<\cdot\}$ is not right-continuous.
--
--   **Formalization Note** $M$ is the set of elements of $L$ equivalent to an equilibrium of Definition 7.1; "$f$ continuous in $m$" is sequential continuity of $m\mapsto f(t,x,m)$ for weak convergence, for every $t\in[0,T]$ and $x$.
--
--   Differences from the source:
--   - reading: (7.7) R̂(m) := arg min_E J(·, m) → R̂(m) = arg max_E J(·, m); reason: J is a profit to be maximized: §7.1 (p.29), Definition 7.1 ('τ^m ∈ arg max'), and the proof of Theorem 7.7 (J(τⁿ, mⁿ⁻¹) ≥ J(τ, mⁿ⁻¹), p.32)
--   - reading: the future-increment σ-field is printed with t ≤ s₁ ≤ s₁ ≤ T → t ≤ s₁ ≤ s₂ ≤ T; reason: the displayed generators are B_{s₂}−B_{s₁}, so the repeated s₁ is a typographical error
--   - reading: the learning procedure … converges to the minimum MFG solution → a least element of M exists and mⁿ converges weakly to each of its representatives, a.e. as in (7.10); reason: the order limit equals the weak limit by Lemma 3.1 and the proof establishes exactly this
--   - reading: E[sup_t (f(t, X_t, µ^ψ_t) + g(t, X_t))] < ∞ (Assumption 7.2) → for some F^B-progressive version µ^ψ; reason: µ^ψ is defined only up to versions
--   - encoding: M ⊂ L; m⁰ = inf L; mⁿ⁺¹ = inf R(mⁿ) → classes of Definition 7.1 equilibria in L; m⁰ a bottom of L; mⁿ⁺¹ a greatest lower bound of R(mⁿ), every choice of representatives; reason: L is a set of classes
--   - encoding: stopping times τ ≤ T P-a.s.; conditional probabilities P[· | F^B_t] P-a.s.; J(τ, m) = E[…] → τ with values in [0, T] everywhere; identities for each (t, A) a.s. (Mathlib conditional expectation of indicators); J in [0, ∞] with f, g ≥ 0; reason: a null-set modification under the usual conditions; nonnegativity is Assumption 7.2 (2)
--   - encoding: weak convergence → WeakConv (survival functions at continuity points); reason: for nondecreasing sequences of sub-probability measures the total masses converge, so it coincides with narrow convergence
--   - encoding: f continuous in m → sequential continuity of m ↦ f(t, x, m) for weak convergence, t ∈ [0, T]; reason: the weak topology is metrizable (p.9)
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §7.3, Theorem 7.7, p.32 (setting pp.29–31)

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb
import Definitions.Def_RepairSched_UsualConditions
import Definitions.Def_SubmodMFG_Supplement_Processes
import Definitions.Def_SubmodMFG_Supplement_StoppingMFG

open MeasureTheory Filter Topology

namespace SubmodMFG.Supplement

/-- **Theorem 7.7** — the optimal-stopping MFG with common noise has least and greatest
equilibria, and the lower learning procedure increases to the least one.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §7.3, Theorem 7.7, p.32: "The set of MFG equilibria M is nonempty with
inf M ∈ M and sup M ∈ M. Moreover, if f is continuous in m, we have that the learning procedure
mⁿ defined inductively by m⁰ = inf L and mⁿ⁺¹ = inf R(mⁿ) is nondecreasing in L and it converges
to the minimum MFG solution."

**Formalization Note.** Standing assumptions of §7.1 and Assumptions 7.2, 7.4. `M` is
`StopModel.equilibria` (classes in `L` of Definition 7.1 equilibria); `inf`, `sup` are
`IsGLB`/`IsLUB` in `L`, `m⁰ = inf L` is a bottom element of `L`, `mⁿ⁺¹` is a greatest lower bound
of `R(mⁿ)` in `L` (every choice of representatives). "f continuous in m" is sequential continuity
of `m ↦ f(t, x, m)` for weak convergence (`WeakConv`; the weak topology is metrizable, p.9).
"Converges to the minimum MFG solution" is: a least element of `M` exists and, for each of its
representatives `e`, `mⁿ_t → e_t` weakly for `P ⊗ dt`-a.e. `(t, ω) ∈ [0, T] × Ω`, as in (7.10). -/
theorem theorem_7_7 {Ω : Type*} [MeasurableSpace Ω] {d₁ d₂ : ℕ} (M : StopModel Ω d₁ d₂)
    (hM : M.Standing) (h72 : M.Assumption72) (h74 : M.Assumption74) :
    (M.equilibria.Nonempty ∧
      (∃ e, IsGLB M.equilibria e ∧ e ∈ M.equilibria) ∧
      (∃ e, IsLUB M.equilibria e ∧ e ∈ M.equilibria)) ∧
    ((∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ x (μ : ℕ → SubProb) (ν : SubProb), WeakConv μ ν →
        Tendsto (fun n => M.f t x (μ n)) atTop (𝓝 (M.f t x ν))) →
      ∀ m : ℕ → M.FlowL, IsBot (m 0) → (∀ n, IsGLB (M.R (m n)) (m (n + 1))) →
        Monotone m ∧ (∃ e, IsLeast M.equilibria e) ∧
        ∀ e, IsLeast M.equilibria e →
          ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) M.T)).prod M.P),
            WeakConv (fun n => (m n).1 p.1 p.2) (e.1 p.1 p.2)) := by sorry

end SubmodMFG.Supplement
