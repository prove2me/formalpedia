-- Prove2me | Theorems.Thm_SubmodMFG_Supplement_theorem_5_9
-- name    : SubmodMFG.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:26:07.264042+00:00
-- url     : https://prove2.me/theorems/fcfb36da-2762-59d4-ac96-7bfe8c9924fc
-- title:
--   Theorem 5.9 (companion theorem) — nonconvex singular-control MFG without common noise: least and greatest equilibria, reached by the inf/sup best-response iterations
-- statement:
--   In the weak-formulation singular-control MFG of §5.2 (Lipschitz drift $b$, constant $\sigma\ge0$, initial law $\nu_0$ with a finite $p$-th moment, costs under Assumption 5.1), let $\mu^{Min},\mu^{Max}\in\mathcal P(\mathbb R)$ satisfy (5.19), let $L$ be the measurable flows with values in $[\mu^{Min},\mu^{Max}]$ $\pi$-a.e. ($\pi=dt+\delta_T$), and let $M\subseteq L$ be the set of MFG equilibria of Definition 5.6. Then:
--
--   1. $M$ is nonempty and $\inf M\in M$, $\sup M\in M$.
--   2. If $f$ and $g$ are continuous in $(x,\mu)$, the sequence $\mu^0=\inf L$, $\mu^{n+1}=\inf R(\mu^n)$ is nondecreasing, a least equilibrium $\underline\mu$ exists, and $\mu^n_t\to\underline\mu_t$ weakly for $\pi$-a.e. $t$.
--   3. Under the same condition, $\mu^0=\sup L$, $\mu^{n+1}=\sup R(\mu^n)$ is nonincreasing, a greatest equilibrium $\bar\mu$ exists, and $\mu^n_t\to\bar\mu_t$ weakly for $\pi$-a.e. $t$.
--
--   Here $R(\mu)=\{P\circ(X^\rho)^{-1}:\rho\text{ optimal for }\mu\}$; optimal controls need not be unique.
--
--   **Formalization Note** The statement holds for every pair $\mu^{Min},\mu^{Max}$ satisfying (5.19). Elements of $L$ are representatives; $M$ and $R(\mu)$ consist of the flows agreeing $\pi$-a.e. with equilibria, respectively optimal marginal-law flows; inf and sup are greatest lower and least upper bounds in $L$.
--
--   Differences from the source:
--   - reading: the learning procedure … converges to the minimum (maximal) MFG solution → a least (greatest) element of M exists and µⁿ converges weakly to each of its representatives, a.e. as in the paper's proofs; 'maximal' read as greatest; reason: the order limit equals the weak limit by Lemma 3.1; the proofs (Theorem 2.6, (7.10)) establish exactly this
--   - reading: µ^Min, µ^Max ∈ P(ℝ) such that (5.19) (p.21: 'we can find') → the theorem for every pair satisfying (5.19); reason: each such pair defines the paper's L
--   - encoding: weak formulation over all filtered probability spaces; X^ρ the unique solution of (5.16); J(ρ, µ) = E^P[…] → sample spaces in Type; X^ρ carried with (5.16) a.s.; J in [−∞, ∞]; reason: uniqueness of the solution (p.20); the cost may be +∞
--   - encoding: M ⊂ L and R(µ) as sets of π-classes → elements of L agreeing π-a.e. with a Definition 5.6 equilibrium, resp. with the marginal laws of an optimal control; reason: ≤st is antisymmetric, so π-a.e. equality is ≤_L-equivalence
--   - encoding: weak convergence → WeakConv (survival functions at continuity points); reason: for probability measures in [µ^Min, µ^Max] and a probability limit it coincides with narrow convergence
--   - encoding: f and g continuous in (x, µ) → ContInXMu: sequential continuity for the weak convergence; reason: the weak topology is metrizable (p.9)
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §5.2.3, Theorem 5.9, p.24 (model pp.20–21)

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb
import Definitions.Def_RepairSched_UsualConditions
import Definitions.Def_SubmodMFG_Supplement_Processes
import Definitions.Def_SubmodMFG_Supplement_SingularCommon
import Definitions.Def_SubmodMFG_Supplement_SingularWeak

open MeasureTheory

namespace SubmodMFG.Supplement

/-- **Theorem 5.9** — the nonconvex singular-control MFG without common noise has least and
greatest equilibria, reached by the inf/sup best-response iterations.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §5.2.3, Theorem 5.9, p.24: "The set of mean field game equilibria M is
nonempty with inf M ∈ M and sup M ∈ M. Moreover, if f and g are continuous in (x, µ), then
(1) the learning procedure µⁿ defined inductively by µ⁰ = inf L and µⁿ⁺¹ = inf R(µⁿ) is
nondecreasing in L and it converges to the minimum MFG solution, (2) the learning procedure µⁿ
defined inductively by µ⁰ = sup L and µⁿ⁺¹ = sup R(µⁿ) is nonincreasing in L and it converges to
the maximal MFG solution."

**Formalization Note.** Standing assumptions of §§5, 5.2.1, for every pair `µ^Min, µ^Max ∈ P(ℝ)`
satisfying (5.19) (p.21: "we can find µ^Min, µ^Max"). `L`, `R`, `M` are `Lset`, `R`,
`equilibria` (Definition 5.6 equilibria, up to `π`-a.e. equality); inf/sup are `IsGLB`/`IsLUB`
in `L`, `µ⁰ = inf L` is a bottom (`sup L` a top) of `L`, every choice of representatives is
covered. "Converges to the minimum (maximal) MFG solution": a least (greatest) element of `M`
exists and `µⁿ_t → e_t` weakly for `π`-a.e. `t`, for each of its representatives `e`; "maximal"
is read as greatest. "Continuous in (x, µ)" is `ContInXMu`. -/
theorem theorem_5_9 (D : SingWeakModel) (hD : D.Standing) (μMin μMax : SubProb)
    (hb : D.Bounds519 μMin μMax) :
    ((D.equilibria μMin μMax).Nonempty ∧
      (∃ e, IsGLB (D.equilibria μMin μMax) e ∧ e ∈ D.equilibria μMin μMax) ∧
      (∃ e, IsLUB (D.equilibria μMin μMax) e ∧ e ∈ D.equilibria μMin μMax)) ∧
    (ContInXMu D.T D.f D.g →
      (∀ m : ℕ → D.Lset μMin μMax, IsBot (m 0) →
          (∀ n, IsGLB (D.R μMin μMax (m n)) (m (n + 1))) →
        Monotone m ∧ (∃ e, IsLeast (D.equilibria μMin μMax) e) ∧
        ∀ e, IsLeast (D.equilibria μMin μMax) e →
          ∀ᵐ t ∂D.π, WeakConv (fun n => (m n).1.1 t) (e.1.1 t)) ∧
      (∀ m : ℕ → D.Lset μMin μMax, IsTop (m 0) →
          (∀ n, IsLUB (D.R μMin μMax (m n)) (m (n + 1))) →
        Antitone m ∧ (∃ e, IsGreatest (D.equilibria μMin μMax) e) ∧
        ∀ e, IsGreatest (D.equilibria μMin μMax) e →
          ∀ᵐ t ∂D.π, WeakConv (fun n => (m n).1.1 t) (e.1.1 t))) := by sorry

end SubmodMFG.Supplement
