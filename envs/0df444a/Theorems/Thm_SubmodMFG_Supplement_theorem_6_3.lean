-- Prove2me | Theorems.Thm_SubmodMFG_Supplement_theorem_6_3
-- name    : SubmodMFG.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:27:21.988116+00:00
-- url     : https://prove2.me/theorems/64de121a-6155-4c84-81cb-7e1035892e69
-- title:
--   Theorem 6.3 (companion theorem; corrected: convex nonempty control set) — MFG with reflecting boundary: least and greatest equilibria, reached by the inf/sup best-response iterations
-- statement:
--   In the reflected MFG of §6, with $A$ compact, nonempty and convex, let $M$ be the set of MFG equilibria of Definition 6.1 (a strict control optimal among all relaxed controls, with $\mu_t=P\circ X_t^{-1}$ for every $t$) in $L=L_M$, and $R$ the best response (6.4). Then:
--
--   1. $M$ is nonempty with $\inf M\in M$ and $\sup M\in M$.
--   2. If $f$ and $g$ are continuous in $(x,\mu)$, the sequence $\mu^0=\inf L$, $\mu^{n+1}=\inf R(\mu^n)$ is nondecreasing, a least equilibrium $\underline\mu$ exists, and $\mu^n_t\to\underline\mu_t$ weakly for $\pi$-a.e. $t$ ($\pi=\delta_0+dt+\delta_T$).
--   3. Under the same condition, $\mu^0=\sup L$, $\mu^{n+1}=\sup R(\mu^n)$ is nonincreasing, a greatest equilibrium $\bar\mu$ exists, and $\mu^n_t\to\bar\mu_t$ weakly for $\pi$-a.e. $t$.
--
--   This applies Theorem 2.6 to mean field games of reflected diffusions, motivated by queueing systems with strategic servers.
--
--   **Formalization Note** Elements of $L_M$ are representatives; $M$ and $R(\mu)$ consist of flows agreeing $\pi$-a.e. with equilibria, respectively with marginal-law flows of optimal relaxed controls; inf and sup are taken in $L_M$.
--
--   Differences from the source:
--   - correction: a compact control set A ⊂ ℝ → A compact, nonempty and convex; reason: for A = {0, 1}, σ = 0, b = 0, l = 0, c = 1, x₀ = M/2, T ≤ M/2, f(t, x, µ) = (x − x₀ − t/2)² + C and g(x, µ) = (x − x₀ − T/2)² + C (C large enough for the growth bound of Assumption 5.1; no µ-dependence, so decreasing differences hold), the relaxed control (δ₀ + δ₁)/2 attains inf J = C(T + 1) while every strict control has X_t − x₀ − t/2 with derivative ±1/2 a.e., hence J > C(T + 1): no strict optimal control exists and M = ∅ (DISPROOF.md); for A = ∅ there are no controls
--   - reading: the learning procedure … converges to the minimum (maximal) MFG solution → a least (greatest) element of M exists and µⁿ converges weakly to each of its representatives, a.e. as in the paper's proofs; 'maximal' read as greatest; reason: the order limit equals the weak limit by Lemma 3.1; the proofs (Theorem 2.6, (7.10)) establish exactly this
--   - reading: σ (not restated in §6); 'is a non empty', 'If' → a constant σ ≥ 0; typos ignored; reason: as in §5.2.1
--   - encoding: M ⊂ L and R(µ) as sets of π-classes → flows of L_M agreeing π-a.e. with a Definition 6.1 equilibrium, resp. with the marginal laws of an optimal relaxed control; reason: ≤st is antisymmetric
--   - encoding: weak convergence → WeakConv (survival functions at continuity points); reason: for probability measures on [0, M] it coincides with narrow convergence
--   - encoding: f and g continuous in (x, µ) → ContInXMu: sequential continuity for the weak convergence; reason: the weak topology is metrizable (p.9)
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §6.3, Theorem 6.3, p.28 (model §6.1–6.2, pp.25–27)

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb
import Definitions.Def_RepairSched_UsualConditions
import Definitions.Def_SubmodMFG_Supplement_Processes
import Definitions.Def_SubmodMFG_Supplement_SingularCommon
import Definitions.Def_SubmodMFG_Supplement_ReflectedMFG

open MeasureTheory

namespace SubmodMFG.Supplement

/-- **Theorem 6.3** — the MFG with reflecting boundary has least and greatest equilibria,
reached by the inf/sup best-response iterations.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §6.3, Theorem 6.3, p.28: "The set of mean field game equilibria M is a non
empty with inf M ∈ M and sup M ∈ M. Moreover, If f and g are continuous in (x, µ), then (1) the
learning procedure µⁿ defined inductively by µ⁰ = inf L and µⁿ⁺¹ = inf R(µⁿ) is nondecreasing in
L and it converges to the minimum MFG solution, (2) the learning procedure µⁿ defined inductively
by µ⁰ = sup L and µⁿ⁺¹ = sup R(µⁿ) is nonincreasing in L and it converges to the maximal MFG
solution."

**Formalization Note.** Standing assumptions of §6 (`ReflModel.Standing`, with `A` convex). `M` is
the set of Definition 6.1 equilibria (up to `π`-a.e. equality) in `L = L_M`; `R` is (6.4);
inf/sup are `IsGLB`/`IsLUB` in `L_M`, `µ⁰ = inf L` a bottom (`sup L` a top) of `L_M`. "Converges
to the minimum (maximal) MFG solution": a least (greatest) element of `M` exists and `µⁿ_t → e_t`
weakly for `π`-a.e. `t`, for each of its representatives `e`; "maximal" is read as greatest. -/
theorem theorem_6_3 (D : ReflModel) (hD : D.Standing) :
    (D.equilibria.Nonempty ∧
      (∃ e, IsGLB D.equilibria e ∧ e ∈ D.equilibria) ∧
      (∃ e, IsLUB D.equilibria e ∧ e ∈ D.equilibria)) ∧
    (ContInXMu D.T D.f D.g →
      (∀ m : ℕ → D.LM, IsBot (m 0) → (∀ n, IsGLB (D.R (m n)) (m (n + 1))) →
        Monotone m ∧ (∃ e, IsLeast D.equilibria e) ∧
        ∀ e, IsLeast D.equilibria e → ∀ᵐ t ∂D.π, WeakConv (fun n => (m n).1 t) (e.1 t)) ∧
      (∀ m : ℕ → D.LM, IsTop (m 0) → (∀ n, IsLUB (D.R (m n)) (m (n + 1))) →
        Antitone m ∧ (∃ e, IsGreatest D.equilibria e) ∧
        ∀ e, IsGreatest D.equilibria e → ∀ᵐ t ∂D.π, WeakConv (fun n => (m n).1 t) (e.1 t))) := by sorry

end SubmodMFG.Supplement
