-- Prove2me | Theorems.Thm_SubmodMFG_theorem_2_6_c
-- name    : SubmodMFG.theorem_2_6_c
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:10.729132+00:00
-- url     : https://prove2.me/theorems/df1c343d-60f5-4b61-b432-e062becaac9d
-- title:
--   Theorem 2.6 c) — the upper learning procedure decreases to the greatest equilibrium
-- statement:
--   Let $(L,\le^L)$ be a complete and Dedekind super complete lattice, $E$ a topological space of strategies, $p:E\to L$ a projection and $J:E\times L\to\mathbb R$ a cost functional satisfying Assumptions 2.1 and 2.3. Write $R(\mu)=p(\arg\min_E J(\cdot,\mu))$ for the best-response set.
--
--   Let $M$ be the set of mean field game equilibria and assume in addition Assumption 2.5. Then the learning procedure
--   $$
--   \overline\mu^0:=\sup L,\qquad\overline\mu^n:=\sup R(\overline\mu^{n-1}),\quad n\in\mathbb N,
--   $$
--   is monotone decreasing and converges to $\sup M$:
--   $$
--   \overline\mu^0\ge^L\overline\mu^1\ge^L\cdots,\qquad \inf_n\overline\mu^n=\sup M .
--   $$
--
--   **Formalization Note** Convergence is the order limit $\inf_n\overline\mu^n=\sup M$, since $L$ carries no topology in Section 2.
--
--   Differences from the source:
--   - encoding: cost functional J : E × L → ℝ → curried J : E → L → ℝ, J ν µ = J(ν, µ); reason: Lean convention; the same functions
--   - encoding: (L, ≤L) complete and Dedekind super complete lattice (Definition A.1) → CompleteLattice L with DedekindSuperComplete L: every nonempty S ⊆ L has countable C, C' ⊆ S with sSup C = sSup S and sInf C' = sInf S; reason: every subset of a complete lattice is bounded, so the boundedness proviso is void; allowing C = ∅ is equivalent (sSup ∅ = sSup S forces S = {⊥}, and C = S works)
--   - encoding: a subsequence (n_j) and convergence ν^{n_j} → ν (Assumption 2.1 (2)) → φ : ℕ → ℕ with StrictMono φ and Tendsto (ν ∘ φ) atTop (𝓝 ν) in the topology of E; reason: the standard encoding of subsequences and convergence
--   - generalization: Assumption 2.5, first sentence, for p(νⁿ) increasing or decreasing → required only when n ↦ p(νⁿ) is StrictMono or StrictAnti; reason: a weaker hypothesis: any model satisfying the paper's assumption (under the nondecreasing or the strict reading of increasing) satisfies the Lean one, so the Lean theorem specializes to the paper's
--   - reading: (νⁿ)ₙ ⊂ {arg min_E J(·, µ) | µ ∈ L} (Assumption 2.5) → ∀ n, ∃ µ, νⁿ ∈ argminSet J µ; reason: the set-builder lists the argmin sets; a point belongs to it when it lies in one of them, µ depending on n (the proof applies it to νⁿ ∈ arg min J(·, µ̲ⁿ⁻¹))
--   - encoding: sup_n µ, inf_n µ (Assumption 2.5 (1), (2)) → ⨆ n, µ n and ⨅ n, µ n; reason: the printed µ stands for µⁿ
--   - encoding: lim inf_n J(νⁿ, µⁿ) (Assumption 2.5 (2)) → Filter.liminf of the EReal-coerced sequence; reason: the extended-real lim inf of the paper; Mathlib's real liminf takes a junk value for sequences unbounded below
--   - encoding: µ̄⁰ := sup L, µ̄ⁿ := sup R(µ̄ⁿ⁻¹) for n ∈ ℕ → upperLearning 0 = ⊤, upperLearning (n+1) = sSup (bestResponse p J (upperLearning n)); reason: the same sequence, indexed from 0
--   - reading: µ̄ⁿ is monotone decreasing and converges to sup M → Antitone (upperLearning p J) ∧ ⨅ n, upperLearning p J n = sSup M; reason: §2 puts no topology on L; the limit of a decreasing sequence in a complete lattice is its infimum; the dual of the proof of b)
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.3, Theorem 2.6 c), p.7

import Mathlib
import Definitions.Def_SubmodMFG_DedekindSuperComplete
import Definitions.Def_SubmodMFG_argminSet
import Definitions.Def_SubmodMFG_bestResponse
import Definitions.Def_SubmodMFG_Assumption21
import Definitions.Def_SubmodMFG_Assumption23
import Definitions.Def_SubmodMFG_equilibria
import Definitions.Def_SubmodMFG_Assumption25
import Definitions.Def_SubmodMFG_upperLearning

namespace SubmodMFG

/-- **Theorem 2.6 c)** — the upper learning procedure
decreases to the greatest equilibrium.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.3, Theorem 2.6 c), p.7: "Moreover, if Assumption 2.5 is satisfied, then [...] c) the
learning procedure µ̄⁰ := sup L and µ̄ⁿ := sup R(µ̄ⁿ⁻¹), for n ∈ ℕ, is monotone decreasing and it
converges to sup M."

**Formalization Note.** Standing hypotheses of §2 (pp.5–6): `L` is a complete (`CompleteLattice`) and
Dedekind super complete lattice, `E` a topological space, `p : E → L`, and `J : E → L → ℝ`
(curried, `J ν µ = J(ν, µ)`) satisfy Assumptions 2.1 and 2.3. `µ̄ⁿ = upperLearning p J n`, `M = equilibria p J`. "Monotone
decreasing" is `Antitone`. `L` carries no topology in §2; "converges to sup M" is the order
limit `⨅ₙ µ̄ⁿ = sup M` (the dual of the proof of b), pp.7–8). `Assumption25` asks its first
condition only along strictly monotone sequences, a weaker hypothesis than the nonincreasing
reading of the paper's "decreasing". -/
theorem theorem_2_6_c {E L : Type*} [TopologicalSpace E] [CompleteLattice L] (p : E → L) (J : E → L → ℝ)
    (hL : DedekindSuperComplete L) (h21 : Assumption21 p J) (h23 : Assumption23 p J) :
    Assumption25 p J →
      Antitone (upperLearning p J) ∧ ⨅ n, upperLearning p J n = sSup (equilibria p J) := by sorry

end SubmodMFG
