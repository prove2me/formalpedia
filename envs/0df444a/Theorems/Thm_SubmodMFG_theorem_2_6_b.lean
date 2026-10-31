-- Prove2me | Theorems.Thm_SubmodMFG_theorem_2_6_b
-- name    : SubmodMFG.theorem_2_6_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:49.128306+00:00
-- url     : https://prove2.me/theorems/f227a1ce-0202-4783-8f2b-63a032fcb606
-- title:
--   Theorem 2.6 b) — the lower learning procedure increases to the least equilibrium
-- statement:
--   Let $(L,\le^L)$ be a complete and Dedekind super complete lattice, $E$ a topological space of strategies, $p:E\to L$ a projection and $J:E\times L\to\mathbb R$ a cost functional satisfying Assumptions 2.1 and 2.3. Write $R(\mu)=p(\arg\min_E J(\cdot,\mu))$ for the best-response set.
--
--   Let $M$ be the set of mean field game equilibria and assume in addition Assumption 2.5. Then the learning procedure
--   $$
--   \underline\mu^0:=\inf L,\qquad\underline\mu^n:=\inf R(\underline\mu^{n-1}),\quad n\in\mathbb N,
--   $$
--   is monotone increasing and converges to $\inf M$:
--   $$
--   \underline\mu^0\le^L\underline\mu^1\le^L\cdots,\qquad \sup_n\underline\mu^n=\inf M .
--   $$
--
--   **Formalization Note** Convergence is the order limit $\sup_n\underline\mu^n=\inf M$, since $L$ carries no topology in Section 2.
--
--   Differences from the source:
--   - encoding: cost functional J : E × L → ℝ → curried J : E → L → ℝ, J ν µ = J(ν, µ); reason: Lean convention; the same functions
--   - encoding: (L, ≤L) complete and Dedekind super complete lattice (Definition A.1) → CompleteLattice L with DedekindSuperComplete L: every nonempty S ⊆ L has countable C, C' ⊆ S with sSup C = sSup S and sInf C' = sInf S; reason: every subset of a complete lattice is bounded, so the boundedness proviso is void; allowing C = ∅ is equivalent (sSup ∅ = sSup S forces S = {⊥}, and C = S works)
--   - encoding: a subsequence (n_j) and convergence ν^{n_j} → ν (Assumption 2.1 (2)) → φ : ℕ → ℕ with StrictMono φ and Tendsto (ν ∘ φ) atTop (𝓝 ν) in the topology of E; reason: the standard encoding of subsequences and convergence
--   - generalization: Assumption 2.5, first sentence, for p(νⁿ) increasing or decreasing → required only when n ↦ p(νⁿ) is StrictMono or StrictAnti; reason: a weaker hypothesis: any model satisfying the paper's assumption (under the nondecreasing or the strict reading of increasing) satisfies the Lean one, so the Lean theorem specializes to the paper's
--   - reading: (νⁿ)ₙ ⊂ {arg min_E J(·, µ) | µ ∈ L} (Assumption 2.5) → ∀ n, ∃ µ, νⁿ ∈ argminSet J µ; reason: the set-builder lists the argmin sets; a point belongs to it when it lies in one of them, µ depending on n (the proof applies it to νⁿ ∈ arg min J(·, µ̲ⁿ⁻¹))
--   - encoding: sup_n µ, inf_n µ (Assumption 2.5 (1), (2)) → ⨆ n, µ n and ⨅ n, µ n; reason: the printed µ stands for µⁿ
--   - encoding: lim inf_n J(νⁿ, µⁿ) (Assumption 2.5 (2)) → Filter.liminf of the EReal-coerced sequence; reason: the extended-real lim inf of the paper; Mathlib's real liminf takes a junk value for sequences unbounded below
--   - encoding: µ̲⁰ := inf L, µ̲ⁿ := inf R(µ̲ⁿ⁻¹) for n ∈ ℕ → lowerLearning 0 = ⊥, lowerLearning (n+1) = sInf (bestResponse p J (lowerLearning n)); reason: the same sequence, indexed from 0
--   - reading: µ̲ⁿ is monotone increasing and converges to inf M → Monotone (lowerLearning p J) ∧ ⨆ n, lowerLearning p J n = sInf M; reason: §2 puts no topology on L; the limit of an increasing sequence in a complete lattice is its supremum, and the proof (pp.7–8) proves exactly µ* := sup_n µ̲ⁿ = inf M
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.3, Theorem 2.6 b), p.7

import Mathlib
import Definitions.Def_SubmodMFG_DedekindSuperComplete
import Definitions.Def_SubmodMFG_argminSet
import Definitions.Def_SubmodMFG_bestResponse
import Definitions.Def_SubmodMFG_Assumption21
import Definitions.Def_SubmodMFG_Assumption23
import Definitions.Def_SubmodMFG_equilibria
import Definitions.Def_SubmodMFG_Assumption25
import Definitions.Def_SubmodMFG_lowerLearning

namespace SubmodMFG

/-- **Theorem 2.6 b)** — the lower learning procedure
increases to the least equilibrium.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.3, Theorem 2.6 b), p.7: "Moreover, if Assumption 2.5 is satisfied, then b) the
learning procedure µ̲⁰ := inf L and µ̲ⁿ := inf R(µ̲ⁿ⁻¹), for n ∈ ℕ, is monotone increasing and it
converges to inf M,"

**Formalization Note.** Standing hypotheses of §2 (pp.5–6): `L` is a complete (`CompleteLattice`) and
Dedekind super complete lattice, `E` a topological space, `p : E → L`, and `J : E → L → ℝ`
(curried, `J ν µ = J(ν, µ)`) satisfy Assumptions 2.1 and 2.3. `µ̲ⁿ = lowerLearning p J n`, `M = equilibria p J`. "Monotone
increasing" is `Monotone`. `L` carries no topology in §2; "converges to inf M" is the order limit
`⨆ₙ µ̲ⁿ = inf M`, which is what the proof (pp.7–8) establishes for the increasing sequence.
`Assumption25` asks its first condition only along strictly monotone sequences, a weaker
hypothesis than the nondecreasing reading of the paper's "increasing". -/
theorem theorem_2_6_b {E L : Type*} [TopologicalSpace E] [CompleteLattice L] (p : E → L) (J : E → L → ℝ)
    (hL : DedekindSuperComplete L) (h21 : Assumption21 p J) (h23 : Assumption23 p J) :
    Assumption25 p J →
      Monotone (lowerLearning p J) ∧ ⨆ n, lowerLearning p J n = sInf (equilibria p J) := by sorry

end SubmodMFG
