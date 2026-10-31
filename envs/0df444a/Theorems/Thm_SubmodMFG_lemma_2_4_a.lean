-- Prove2me | Theorems.Thm_SubmodMFG_lemma_2_4_a
-- name    : SubmodMFG.lemma_2_4_a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:45.669998+00:00
-- url     : https://prove2.me/theorems/fea073b8-b80e-4e3d-978f-9cd28f489c1e
-- title:
--   Lemma 2.4 a) — the best-response set $R(\mu)$ is directed
-- statement:
--   Let $(L,\le^L)$ be a complete and Dedekind super complete lattice, $E$ a topological space of strategies, $p:E\to L$ a projection and $J:E\times L\to\mathbb R$ a cost functional satisfying Assumptions 2.1 and 2.3. Write $R(\mu)=p(\arg\min_E J(\cdot,\mu))$ for the best-response set.
--
--   Then for every $\mu\in L$ the set $R(\mu)$ is **directed**: for every $\eta^1,\eta^2\in R(\mu)$ there exist $\eta^\wedge,\eta^\vee\in R(\mu)$ such that
--   $$
--   \eta^\wedge\le^L\eta^1\wedge^L\eta^2\qquad\text{and}\qquad\eta^\vee\ge^L\eta^1\vee^L\eta^2 .
--   $$
--
--   This is the first structural property of the best responses; with Dedekind super completeness it yields that $\inf R(\mu)$ and $\sup R(\mu)$ are best responses (Lemma 2.4 c)).
--
--   Differences from the source:
--   - encoding: cost functional J : E × L → ℝ → curried J : E → L → ℝ, J ν µ = J(ν, µ); reason: Lean convention; the same functions
--   - encoding: (L, ≤L) complete and Dedekind super complete lattice (Definition A.1) → CompleteLattice L with DedekindSuperComplete L: every nonempty S ⊆ L has countable C, C' ⊆ S with sSup C = sSup S and sInf C' = sInf S; reason: every subset of a complete lattice is bounded, so the boundedness proviso is void; allowing C = ∅ is equivalent (sSup ∅ = sSup S forces S = {⊥}, and C = S works)
--   - encoding: a subsequence (n_j) and convergence ν^{n_j} → ν (Assumption 2.1 (2)) → φ : ℕ → ℕ with StrictMono φ and Tendsto (ν ∘ φ) atTop (𝓝 ν) in the topology of E; reason: the standard encoding of subsequences and convergence
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.2, Lemma 2.4 a), p.6

import Mathlib
import Definitions.Def_SubmodMFG_DedekindSuperComplete
import Definitions.Def_SubmodMFG_argminSet
import Definitions.Def_SubmodMFG_bestResponse
import Definitions.Def_SubmodMFG_Assumption21
import Definitions.Def_SubmodMFG_Assumption23

namespace SubmodMFG

/-- **Lemma 2.4 a)** — the set of best responses is directed.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.2, Lemma 2.4 a), p.6: "Under Assumptions 2.1 and 2.3 we have that: a) The set R(µ) is
directed, i.e., for every η¹, η² ∈ R(µ), there exist η^∧, η^∨ ∈ R(µ) such that
η^∧ ≤^L η¹ ∧^L η² and η^∨ ≥^L η¹ ∨^L η²."

**Formalization Note.** Standing hypotheses of §2 (pp.5–6): `L` is a complete (`CompleteLattice`) and
Dedekind super complete lattice, `E` a topological space, `p : E → L`, and `J : E → L → ℝ`
(curried, `J ν µ = J(ν, µ)`) satisfy Assumptions 2.1 and 2.3. -/
theorem lemma_2_4_a {E L : Type*} [TopologicalSpace E] [CompleteLattice L] (p : E → L) (J : E → L → ℝ)
    (hL : DedekindSuperComplete L) (h21 : Assumption21 p J) (h23 : Assumption23 p J) :
    ∀ μ : L, ∀ η₁ ∈ bestResponse p J μ, ∀ η₂ ∈ bestResponse p J μ,
      (∃ η ∈ bestResponse p J μ, η ≤ η₁ ⊓ η₂) ∧ (∃ η ∈ bestResponse p J μ, η₁ ⊔ η₂ ≤ η) := by sorry

end SubmodMFG
