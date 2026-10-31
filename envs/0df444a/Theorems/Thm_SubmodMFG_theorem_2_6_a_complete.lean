-- Prove2me | Theorems.Thm_SubmodMFG_theorem_2_6_a_complete
-- name    : SubmodMFG.theorem_2_6_a_complete
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:36.611477+00:00
-- url     : https://prove2.me/theorems/142adc2d-0421-495f-9679-30f01e3fec3e
-- title:
--   Theorem 2.6 a), second sentence — single-valued best responses give a complete lattice of equilibria
-- statement:
--   Let $(L,\le^L)$ be a complete and Dedekind super complete lattice, $E$ a topological space of strategies, $p:E\to L$ a projection and $J:E\times L\to\mathbb R$ a cost functional satisfying Assumptions 2.1 and 2.3. Write $R(\mu)=p(\arg\min_E J(\cdot,\mu))$ for the best-response set.
--
--   Let $M$ be the set of mean field game equilibria. If $R(\mu)$ is a singleton for every $\mu\in L$, then $M$ is a nonempty complete lattice: $M\neq\emptyset$, and every nonempty subset of $M$ has a least upper bound and a greatest lower bound in $M$ (with the order of $L$).
--
--   Differences from the source:
--   - encoding: cost functional J : E × L → ℝ → curried J : E → L → ℝ, J ν µ = J(ν, µ); reason: Lean convention; the same functions
--   - encoding: (L, ≤L) complete and Dedekind super complete lattice (Definition A.1) → CompleteLattice L with DedekindSuperComplete L: every nonempty S ⊆ L has countable C, C' ⊆ S with sSup C = sSup S and sInf C' = sInf S; reason: every subset of a complete lattice is bounded, so the boundedness proviso is void; allowing C = ∅ is equivalent (sSup ∅ = sSup S forces S = {⊥}, and C = S works)
--   - encoding: a subsequence (n_j) and convergence ν^{n_j} → ν (Assumption 2.1 (2)) → φ : ℕ → ℕ with StrictMono φ and Tendsto (ν ∘ φ) atTop (𝓝 ν) in the topology of E; reason: the standard encoding of subsequences and convergence
--   - encoding: R(µ) is a singleton for all µ ∈ L → ∀ µ, ∃ x, bestResponse p J µ = {x}; reason: the same condition
--   - reading: M is a nonempty complete lattice → M nonempty, and every nonempty F ⊆ M has a least upper bound and a greatest lower bound in M with the order induced from L (IsLUB/IsGLB in the subtype); reason: complete per Definition A.1 a); the order on M is the one inherited from L; suprema taken in L (a complete sublattice) are not claimed
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.3, Theorem 2.6 a), second sentence, p.7

import Mathlib
import Definitions.Def_SubmodMFG_DedekindSuperComplete
import Definitions.Def_SubmodMFG_argminSet
import Definitions.Def_SubmodMFG_bestResponse
import Definitions.Def_SubmodMFG_Assumption21
import Definitions.Def_SubmodMFG_Assumption23
import Definitions.Def_SubmodMFG_equilibria

namespace SubmodMFG

/-- **Theorem 2.6 a), second sentence** — with
single-valued best responses, the equilibria form a nonempty complete lattice.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.3, Theorem 2.6 a), p.7: "If R(µ) is a singleton for all µ ∈ L, then M is a nonempty
complete lattice."

**Formalization Note.** Standing hypotheses of §2 (pp.5–6): `L` is a complete (`CompleteLattice`) and
Dedekind super complete lattice, `E` a topological space, `p : E → L`, and `J : E → L → ℝ`
(curried, `J ν µ = J(ν, µ)`) satisfy Assumptions 2.1 and 2.3. "Complete lattice" is Definition A.1 a), p.33: every nonempty
subset has a least upper bound and a greatest lower bound; here in `M = equilibria p J` with the
order induced from `L` (`IsLUB`/`IsGLB` in the subtype), not suprema taken in `L`. The lattice
property (finite nonempty subsets) is a special case. -/
theorem theorem_2_6_a_complete {E L : Type*} [TopologicalSpace E] [CompleteLattice L] (p : E → L) (J : E → L → ℝ)
    (hL : DedekindSuperComplete L) (h21 : Assumption21 p J) (h23 : Assumption23 p J) :
    (∀ μ : L, ∃ x : L, bestResponse p J μ = {x}) →
      (equilibria p J).Nonempty ∧
        (∀ F : Set (equilibria p J), F.Nonempty → ∃ b, IsLUB F b) ∧
        (∀ F : Set (equilibria p J), F.Nonempty → ∃ b, IsGLB F b) := by sorry

end SubmodMFG
