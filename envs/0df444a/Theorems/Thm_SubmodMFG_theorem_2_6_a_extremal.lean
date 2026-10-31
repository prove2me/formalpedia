-- Prove2me | Theorems.Thm_SubmodMFG_theorem_2_6_a_extremal
-- name    : SubmodMFG.theorem_2_6_a_extremal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:38.523799+00:00
-- url     : https://prove2.me/theorems/7647df46-8754-49b9-86b8-68aad270f303
-- title:
--   Theorem 2.6 a), first sentence — least and greatest equilibria exist
-- statement:
--   Let $(L,\le^L)$ be a complete and Dedekind super complete lattice, $E$ a topological space of strategies, $p:E\to L$ a projection and $J:E\times L\to\mathbb R$ a cost functional satisfying Assumptions 2.1 and 2.3. Write $R(\mu)=p(\arg\min_E J(\cdot,\mu))$ for the best-response set.
--
--   Let $M=\{\mu\in L:\mu\in R(\mu)\}$ be the set of mean field game equilibria. Then $M$ is nonempty and
--   $$
--   \inf M\in M\qquad\text{and}\qquad\sup M\in M,
--   $$
--   i.e. there are a least and a greatest equilibrium.
--
--   Differences from the source:
--   - encoding: cost functional J : E × L → ℝ → curried J : E → L → ℝ, J ν µ = J(ν, µ); reason: Lean convention; the same functions
--   - encoding: (L, ≤L) complete and Dedekind super complete lattice (Definition A.1) → CompleteLattice L with DedekindSuperComplete L: every nonempty S ⊆ L has countable C, C' ⊆ S with sSup C = sSup S and sInf C' = sInf S; reason: every subset of a complete lattice is bounded, so the boundedness proviso is void; allowing C = ∅ is equivalent (sSup ∅ = sSup S forces S = {⊥}, and C = S works)
--   - encoding: a subsequence (n_j) and convergence ν^{n_j} → ν (Assumption 2.1 (2)) → φ : ℕ → ℕ with StrictMono φ and Tendsto (ν ∘ φ) atTop (𝓝 ν) in the topology of E; reason: the standard encoding of subsequences and convergence
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.3, Theorem 2.6 a), first sentence, p.7

import Mathlib
import Definitions.Def_SubmodMFG_DedekindSuperComplete
import Definitions.Def_SubmodMFG_argminSet
import Definitions.Def_SubmodMFG_bestResponse
import Definitions.Def_SubmodMFG_Assumption21
import Definitions.Def_SubmodMFG_Assumption23
import Definitions.Def_SubmodMFG_equilibria

namespace SubmodMFG

/-- **Theorem 2.6 a), first sentence** — least and greatest
equilibria exist.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.3, Theorem 2.6 a), p.7: "Under Assumptions 2.1 and 2.3 we have that a) the set of mean
field game equilibria M is nonempty with inf M ∈ M and sup M ∈ M."

**Formalization Note.** Standing hypotheses of §2 (pp.5–6): `L` is a complete (`CompleteLattice`) and
Dedekind super complete lattice, `E` a topological space, `p : E → L`, and `J : E → L → ℝ`
(curried, `J ν µ = J(ν, µ)`) satisfy Assumptions 2.1 and 2.3. `M = equilibria p J = {µ | µ ∈ R(µ)}`; `inf M` and `sup M` are
`sInf`/`sSup` in `L`. -/
theorem theorem_2_6_a_extremal {E L : Type*} [TopologicalSpace E] [CompleteLattice L] (p : E → L) (J : E → L → ℝ)
    (hL : DedekindSuperComplete L) (h21 : Assumption21 p J) (h23 : Assumption23 p J) :
    (equilibria p J).Nonempty ∧ sInf (equilibria p J) ∈ equilibria p J ∧
      sSup (equilibria p J) ∈ equilibria p J := by sorry

end SubmodMFG
