-- Prove2me | Theorems.Thm_SubmodMFG_Supplement_lemma_5_8
-- name    : SubmodMFG.Supplement.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:25:42.019461+00:00
-- url     : https://prove2.me/theorems/dc226e4a-dda7-4ada-ad8a-ee12048e5d51
-- title:
--   Lemma 5.8 — the singular-control rules admit operations $\wedge^E,\vee^E:E^M\times E^M\to E$ satisfying Assumption 2.3
-- statement:
--   In the weak formulation of §5.2 (singular controls $\rho=(\Omega,\mathcal F,\mathbb F,P,x_0,W,\xi)$ with state $X^\rho_t=x_0+\int_0^tb(s,X^\rho_s)ds+\sigma W_t+\xi_t$, control rules $\nu^\rho=P\circ(x_0,W,X^\rho,\xi)^{-1}$, $J(\nu^\rho,\mu)=J(\rho,\mu)$ and $p(\nu^\rho)=P\circ(X^\rho)^{-1}$), let $E^M$ be the rules of controls with $E^P[|X^\rho_t|^p+\xi_T^p]\le M$ for all $t$. There exist operations $\wedge^E,\vee^E:E^M\times E^M\to E$ such that, for all $\nu,\bar\nu\in E^M$:
--
--   1. $p(\nu\wedge^E\bar\nu)\le_L p\nu\wedge_L p\bar\nu\le_L p\nu\vee_L p\bar\nu\le_L p(\nu\vee^E\bar\nu)$;
--   2. for all flows $\mu\le_L\bar\mu$,
--   $$J(\nu\vee^E\bar\nu,\bar\mu)-J(\bar\nu,\bar\mu)\le J(\nu\vee^E\bar\nu,\mu)-J(\bar\nu,\mu)\le J(\nu,\mu)-J(\nu\wedge^E\bar\nu,\mu).$$
--
--   This verifies the submodularity conditions of Assumption 2.3 for the nonconvex singular-control game, the key step reducing Theorem 5.9 to Theorem 2.6.
--
--   **Formalization Note** $\le_L$ is $\pi$-a.e. first-order stochastic dominance, $\pi=dt+\delta_T$; condition 1 is written through the lattice operations of $\mathcal M_{\le1}$. Condition 2 is written additively ($a-b\le c-d$ as $a+d\le c+b$) in $[-\infty,\infty]$.
--
--   Differences from the source:
--   - generalization: the constant M of (5.18); µ, µ̄ ∈ L with µ ≤_L µ̄ → every K > 0; every pair of measurable flows of probability measures with µ ≤ µ̄ π-a.e.; reason: L is a set of such flows and M is one such constant; the proof (pp.21–24) uses only the moment bound and Assumption 5.1
--   - encoding: condition 1 of Assumption 2.3 with ∧_L, ∨_L → p(ν ∧ ν̄) ≤ pν, p(ν ∧ ν̄) ≤ pν̄, pν ≤ p(ν ∨ ν̄), pν̄ ≤ p(ν ∨ ν̄), survival-function-wise π-a.e.; reason: a ≤ b ∧ c iff a ≤ b and a ≤ c; the middle inequality holds in every lattice
--   - encoding: differences of real costs → additive form in EReal; reason: equivalent for finite values, which the costs on E^M and of ∧, ∨ have; avoids ∞ − ∞
--   - encoding: canonical space ℝ × C × D × D↑ with Borel σ-algebras; J(ν^ρ, µ) := J(ρ, µ) → ℝ × (ℝ^[0,T])³ with the product σ-algebra; JE evaluates J at a chosen control realizing the rule; reason: the cylinder σ-algebra is the Borel one on C and D; J depends only on the law of (x₀, W, X^ρ, ξ)
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §5.2.3, Lemma 5.8, p.21 (proof pp.21–24; Assumption 2.3, p.6)

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb
import Definitions.Def_RepairSched_UsualConditions
import Definitions.Def_SubmodMFG_Supplement_Processes
import Definitions.Def_SubmodMFG_Supplement_SingularCommon
import Definitions.Def_SubmodMFG_Supplement_SingularWeak

open MeasureTheory

namespace SubmodMFG.Supplement

/-- **Lemma 5.8** — the control rules of the weak-formulation singular-control problem admit
operations `∧^E, ∨^E : E^M × E^M → E` satisfying Assumption 2.3.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §5.2.3, Lemma 5.8, p.21: "There exists two operations ∧^E, ∨^E :
E^M × E^M → E satisfying Assumption 2.3." Assumption 2.3, p.6: "(1) p(ν ∧^E ν̄) ≤^L pν ∧^L pν̄ ≤^L
pν ∨^L pν̄ ≤^L p(ν ∨^E ν̄), for each ν, ν̄ ∈ E. (2) J(ν ∨^E ν̄, µ̄) − J(ν̄, µ̄) ≤ J(ν ∨^E ν̄, µ) −
J(ν̄, µ) ≤ J(ν, µ) − J(ν ∧^E ν̄, µ), for each ν, ν̄ ∈ E and µ, µ̄ ∈ L with µ ≤^L µ̄."

**Formalization Note.** Standing assumptions of §§5, 5.2.1 (`SingWeakModel.Standing`). The bound
`M` of (5.18) is any `K > 0`; the operations are functions on measures, with values in `E` on
`E^M × E^M`. Condition (1) is written through the lattice operations of `M≤1`
(`a ≤ b ∧ c` iff `a ≤ b` and `a ≤ c`; the middle inequality holds in every lattice), `π`-a.e. as
in the order `≤_L` of p.21. Condition (2) is required for every pair `µ ≤ µ̄` of measurable flows
of probabilities (a superset of `L`), and is written additively, `a − b ≤ c − d` as
`a + d ≤ c + b`, in `[−∞, ∞]`. -/
theorem lemma_5_8 (D : SingWeakModel) (hD : D.Standing) :
    ∀ K : ℝ, 0 < K → ∃ meet join : Measure D.Can → Measure D.Can → Measure D.Can,
      (∀ ν ∈ D.EM K, ∀ ν' ∈ D.EM K, meet ν ν' ∈ D.E ∧ join ν ν' ∈ D.E) ∧
      (∀ ν ∈ D.EM K, ∀ ν' ∈ D.EM K, ∀ᵐ t ∂D.π, ∀ s : ℝ,
        D.pE (meet ν ν') t (Set.Ioi s) ≤ D.pE ν t (Set.Ioi s) ∧
        D.pE (meet ν ν') t (Set.Ioi s) ≤ D.pE ν' t (Set.Ioi s) ∧
        D.pE ν t (Set.Ioi s) ≤ D.pE (join ν ν') t (Set.Ioi s) ∧
        D.pE ν' t (Set.Ioi s) ≤ D.pE (join ν ν') t (Set.Ioi s)) ∧
      (∀ ν ∈ D.EM K, ∀ ν' ∈ D.EM K, ∀ μ μ' : D.Flow, μ ≤ μ' →
        D.JE (join ν ν') μ'.1 + D.JE ν' μ.1 ≤ D.JE (join ν ν') μ.1 + D.JE ν' μ'.1 ∧
        D.JE (join ν ν') μ.1 + D.JE (meet ν ν') μ.1 ≤ D.JE ν μ.1 + D.JE ν' μ.1) := by sorry

end SubmodMFG.Supplement
