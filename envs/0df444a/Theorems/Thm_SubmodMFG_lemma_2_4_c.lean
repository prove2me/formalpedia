-- Prove2me | Theorems.Thm_SubmodMFG_lemma_2_4_c
-- name    : SubmodMFG.lemma_2_4_c
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:54.173578+00:00
-- url     : https://prove2.me/theorems/89bd50fa-3274-4e5c-809f-7790c3db7256
-- title:
--   Lemma 2.4 c) — $\inf R(\mu)$ and $\sup R(\mu)$ are best responses
-- statement:
--   Let $(L,\le^L)$ be a complete and Dedekind super complete lattice, $E$ a topological space of strategies, $p:E\to L$ a projection and $J:E\times L\to\mathbb R$ a cost functional satisfying Assumptions 2.1 and 2.3. Write $R(\mu)=p(\arg\min_E J(\cdot,\mu))$ for the best-response set.
--
--   Then for every $\mu\in L$,
--   $$
--   \inf R(\mu)\in R(\mu)\qquad\text{and}\qquad\sup R(\mu)\in R(\mu).
--   $$
--
--   Hence a fixed point of $\mu\mapsto\inf R(\mu)$ or of $\mu\mapsto\sup R(\mu)$ is a mean field game equilibrium.
--
--   Differences from the source:
--   - encoding: cost functional J : E × L → ℝ → curried J : E → L → ℝ, J ν µ = J(ν, µ); reason: Lean convention; the same functions
--   - encoding: (L, ≤L) complete and Dedekind super complete lattice (Definition A.1) → CompleteLattice L with DedekindSuperComplete L: every nonempty S ⊆ L has countable C, C' ⊆ S with sSup C = sSup S and sInf C' = sInf S; reason: every subset of a complete lattice is bounded, so the boundedness proviso is void; allowing C = ∅ is equivalent (sSup ∅ = sSup S forces S = {⊥}, and C = S works)
--   - encoding: a subsequence (n_j) and convergence ν^{n_j} → ν (Assumption 2.1 (2)) → φ : ℕ → ℕ with StrictMono φ and Tendsto (ν ∘ φ) atTop (𝓝 ν) in the topology of E; reason: the standard encoding of subsequences and convergence
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.2, Lemma 2.4 c), p.6

import Mathlib
import Definitions.Def_SubmodMFG_DedekindSuperComplete
import Definitions.Def_SubmodMFG_argminSet
import Definitions.Def_SubmodMFG_bestResponse
import Definitions.Def_SubmodMFG_Assumption21
import Definitions.Def_SubmodMFG_Assumption23

namespace SubmodMFG

/-- **Lemma 2.4 c)** — the infimum and the supremum of the best responses
are best responses.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.2, Lemma 2.4 c), p.6: "Under Assumptions 2.1 and 2.3 we have that: c) For every
µ ∈ L, inf R(µ) ∈ R(µ) and sup R(µ) ∈ R(µ)."

**Formalization Note.** Standing hypotheses of §2 (pp.5–6): `L` is a complete (`CompleteLattice`) and
Dedekind super complete lattice, `E` a topological space, `p : E → L`, and `J : E → L → ℝ`
(curried, `J ν µ = J(ν, µ)`) satisfy Assumptions 2.1 and 2.3. The infimum and supremum are `sInf`/`sSup` in `L`. -/
theorem lemma_2_4_c {E L : Type*} [TopologicalSpace E] [CompleteLattice L] (p : E → L) (J : E → L → ℝ)
    (hL : DedekindSuperComplete L) (h21 : Assumption21 p J) (h23 : Assumption23 p J) :
    ∀ μ : L, sInf (bestResponse p J μ) ∈ bestResponse p J μ ∧
      sSup (bestResponse p J μ) ∈ bestResponse p J μ := by sorry

end SubmodMFG
