-- Prove2me | Theorems.Thm_SubmodMFG_theorem_2_6
-- name    : SubmodMFG.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:55.175618+00:00
-- url     : https://prove2.me/theorems/fa3ed4a8-e5d8-42b4-86c4-9448e7000089
-- title:
--   Theorem 2.6 — least and greatest mean field game equilibria, reached by the learning procedures
-- statement:
--   Let $(L,\le^L)$ be a complete and Dedekind super complete lattice, $E$ a topological space of strategies, $p:E\to L$ a projection and $J:E\times L\to\mathbb R$ a cost functional satisfying Assumptions 2.1 and 2.3. Write $R(\mu)=p(\arg\min_E J(\cdot,\mu))$ for the best-response set.
--
--   Let $M=\{\mu\in L:\mu\in R(\mu)\}$ be the set of mean field game equilibria. Then:
--
--   1. (a) $M$ is nonempty with $\inf M\in M$ and $\sup M\in M$. If $R(\mu)$ is a singleton for all $\mu\in L$, then $M$ is a nonempty complete lattice.
--
--   Moreover, if Assumption 2.5 is satisfied, then
--
--   2. (b) the learning procedure $\underline\mu^0:=\inf L$, $\underline\mu^n:=\inf R(\underline\mu^{n-1})$ for $n\in\mathbb N$ is monotone increasing and converges to $\inf M$:
--   $$
--   \sup_n\underline\mu^n=\inf M;
--   $$
--   3. (c) the learning procedure $\overline\mu^0:=\sup L$, $\overline\mu^n:=\sup R(\overline\mu^{n-1})$ for $n\in\mathbb N$ is monotone decreasing and converges to $\sup M$:
--   $$
--   \inf_n\overline\mu^n=\sup M .
--   $$
--
--   This is the main result of the abstract part of the paper: under submodularity, an abstract mean field game has a least and a greatest equilibrium, and both are computable by iterating the extremal best responses. Sections 4–7 obtain existence and approximation results for concrete mean field games by verifying its assumptions.
--
--   **Formalization Note** "Complete lattice" is Definition A.1 a) in the order induced on $M$. Convergence of the learning procedures is the order limit (supremum, resp. infimum of the monotone sequence), since $L$ carries no topology in Section 2.
--
--   Differences from the source:
--   - encoding: cost functional J : E × L → ℝ → curried J : E → L → ℝ, J ν µ = J(ν, µ); reason: Lean convention; the same functions
--   - encoding: (L, ≤L) complete and Dedekind super complete lattice (Definition A.1) → CompleteLattice L with DedekindSuperComplete L: every nonempty S ⊆ L has countable C, C' ⊆ S with sSup C = sSup S and sInf C' = sInf S; reason: every subset of a complete lattice is bounded, so the boundedness proviso is void; allowing C = ∅ is equivalent (sSup ∅ = sSup S forces S = {⊥}, and C = S works)
--   - encoding: a subsequence (n_j) and convergence ν^{n_j} → ν (Assumption 2.1 (2)) → φ : ℕ → ℕ with StrictMono φ and Tendsto (ν ∘ φ) atTop (𝓝 ν) in the topology of E; reason: the standard encoding of subsequences and convergence
--   - encoding: R(µ) is a singleton for all µ ∈ L → ∀ µ, ∃ x, bestResponse p J µ = {x}; reason: the same condition
--   - reading: M is a nonempty complete lattice → M nonempty, and every nonempty F ⊆ M has a least upper bound and a greatest lower bound in M with the order induced from L (IsLUB/IsGLB in the subtype); reason: complete per Definition A.1 a); the order on M is the one inherited from L; suprema taken in L (a complete sublattice) are not claimed
--   - generalization: Assumption 2.5, first sentence, for p(νⁿ) increasing or decreasing → required only when n ↦ p(νⁿ) is StrictMono or StrictAnti; reason: a weaker hypothesis: any model satisfying the paper's assumption (under the nondecreasing or the strict reading of increasing) satisfies the Lean one, so the Lean theorem specializes to the paper's
--   - reading: (νⁿ)ₙ ⊂ {arg min_E J(·, µ) | µ ∈ L} (Assumption 2.5) → ∀ n, ∃ µ, νⁿ ∈ argminSet J µ; reason: the set-builder lists the argmin sets; a point belongs to it when it lies in one of them, µ depending on n (the proof applies it to νⁿ ∈ arg min J(·, µ̲ⁿ⁻¹))
--   - encoding: sup_n µ, inf_n µ (Assumption 2.5 (1), (2)) → ⨆ n, µ n and ⨅ n, µ n; reason: the printed µ stands for µⁿ
--   - encoding: lim inf_n J(νⁿ, µⁿ) (Assumption 2.5 (2)) → Filter.liminf of the EReal-coerced sequence; reason: the extended-real lim inf of the paper; Mathlib's real liminf takes a junk value for sequences unbounded below
--   - encoding: µ̲⁰ := inf L, µ̲ⁿ := inf R(µ̲ⁿ⁻¹) for n ∈ ℕ → lowerLearning 0 = ⊥, lowerLearning (n+1) = sInf (bestResponse p J (lowerLearning n)); reason: the same sequence, indexed from 0
--   - encoding: µ̄⁰ := sup L, µ̄ⁿ := sup R(µ̄ⁿ⁻¹) for n ∈ ℕ → upperLearning 0 = ⊤, upperLearning (n+1) = sSup (bestResponse p J (upperLearning n)); reason: the same sequence, indexed from 0
--   - reading: µ̲ⁿ is monotone increasing and converges to inf M → Monotone (lowerLearning p J) ∧ ⨆ n, lowerLearning p J n = sInf M; reason: §2 puts no topology on L; the limit of an increasing sequence in a complete lattice is its supremum, and the proof (pp.7–8) proves exactly µ* := sup_n µ̲ⁿ = inf M
--   - reading: µ̄ⁿ is monotone decreasing and converges to sup M → Antitone (upperLearning p J) ∧ ⨅ n, upperLearning p J n = sSup M; reason: §2 puts no topology on L; the limit of a decreasing sequence in a complete lattice is its infimum; the dual of the proof of b)
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.3, Theorem 2.6, p.7

import Mathlib
import Definitions.Def_SubmodMFG_DedekindSuperComplete
import Definitions.Def_SubmodMFG_argminSet
import Definitions.Def_SubmodMFG_bestResponse
import Definitions.Def_SubmodMFG_Assumption21
import Definitions.Def_SubmodMFG_Assumption23
import Definitions.Def_SubmodMFG_equilibria
import Definitions.Def_SubmodMFG_Assumption25
import Definitions.Def_SubmodMFG_lowerLearning
import Definitions.Def_SubmodMFG_upperLearning

namespace SubmodMFG

/-- **Theorem 2.6** — existence of least and greatest
mean field game equilibria, and their approximation by the learning procedures.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.3, Theorem 2.6, p.7: "Under Assumptions 2.1 and 2.3 we have that
a) the set of mean field game equilibria M is nonempty with inf M ∈ M and sup M ∈ M.
If R(µ) is a singleton for all µ ∈ L, then M is a nonempty complete lattice.
Moreover, if Assumption 2.5 is satisfied, then
b) the learning procedure µ̲⁰ := inf L and µ̲ⁿ := inf R(µ̲ⁿ⁻¹), for n ∈ ℕ, is monotone increasing
and it converges to inf M,
c) the learning procedure µ̄⁰ := sup L and µ̄ⁿ := sup R(µ̄ⁿ⁻¹), for n ∈ ℕ, is monotone decreasing
and it converges to sup M."

**Formalization Note.** Standing hypotheses of §2 (pp.5–6): `L` is a complete (`CompleteLattice`) and
Dedekind super complete lattice, `E` a topological space, `p : E → L`, and `J : E → L → ℝ`
(curried, `J ν µ = J(ν, µ)`) satisfy Assumptions 2.1 and 2.3. `M = equilibria p J`. The complete-lattice clause is Definition
A.1 a), p.33 (every nonempty subset has a least upper bound and a greatest lower bound) in the
order induced on `M` (`IsLUB`/`IsGLB` in the subtype). `µ̲ⁿ = lowerLearning p J n` and
`µ̄ⁿ = upperLearning p J n`; "converges to inf M / sup M" is the order limit `⨆ₙ µ̲ⁿ = inf M`,
`⨅ₙ µ̄ⁿ = sup M` (`L` carries no topology in §2). `Assumption25` asks its first condition only
along strictly monotone sequences, a weaker hypothesis than the nondecreasing reading of the
paper's "increasing or decreasing". -/
theorem theorem_2_6 {E L : Type*} [TopologicalSpace E] [CompleteLattice L] (p : E → L) (J : E → L → ℝ)
    (hL : DedekindSuperComplete L) (h21 : Assumption21 p J) (h23 : Assumption23 p J) :
    ((equilibria p J).Nonempty ∧ sInf (equilibria p J) ∈ equilibria p J ∧
        sSup (equilibria p J) ∈ equilibria p J) ∧
    ((∀ μ : L, ∃ x : L, bestResponse p J μ = {x}) →
        (equilibria p J).Nonempty ∧
          (∀ F : Set (equilibria p J), F.Nonempty → ∃ b, IsLUB F b) ∧
          (∀ F : Set (equilibria p J), F.Nonempty → ∃ b, IsGLB F b)) ∧
    (Assumption25 p J →
        (Monotone (lowerLearning p J) ∧ ⨆ n, lowerLearning p J n = sInf (equilibria p J)) ∧
        (Antitone (upperLearning p J) ∧ ⨅ n, upperLearning p J n = sSup (equilibria p J))) := by sorry

end SubmodMFG
