-- Prove2me | Theorems.Thm_SubmodMFG_lemma_2_4_b
-- name    : SubmodMFG.lemma_2_4_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:52.024447+00:00
-- url     : https://prove2.me/theorems/8d19e015-3e28-47fa-b0a7-0f760e4e4d29
-- title:
--   Lemma 2.4 b) — $\inf R(\mu)$ and $\sup R(\mu)$ are monotone in $\mu$
-- statement:
--   Let $(L,\le^L)$ be a complete and Dedekind super complete lattice, $E$ a topological space of strategies, $p:E\to L$ a projection and $J:E\times L\to\mathbb R$ a cost functional satisfying Assumptions 2.1 and 2.3. Write $R(\mu)=p(\arg\min_E J(\cdot,\mu))$ for the best-response set.
--
--   Then for all $\mu,\bar\mu\in L$ with $\mu\le^L\bar\mu$,
--   $$
--   \inf R(\mu)\le^L\inf R(\bar\mu)\qquad\text{and}\qquad\sup R(\mu)\le^L\sup R(\bar\mu).
--   $$
--
--   The maps $\mu\mapsto\inf R(\mu)$ and $\mu\mapsto\sup R(\mu)$ are therefore monotone self-maps of the complete lattice $L$, to which Tarski's fixed point theorem applies in Theorem 2.6 a).
--
--   Differences from the source:
--   - encoding: cost functional J : E × L → ℝ → curried J : E → L → ℝ, J ν µ = J(ν, µ); reason: Lean convention; the same functions
--   - encoding: (L, ≤L) complete and Dedekind super complete lattice (Definition A.1) → CompleteLattice L with DedekindSuperComplete L: every nonempty S ⊆ L has countable C, C' ⊆ S with sSup C = sSup S and sInf C' = sInf S; reason: every subset of a complete lattice is bounded, so the boundedness proviso is void; allowing C = ∅ is equivalent (sSup ∅ = sSup S forces S = {⊥}, and C = S works)
--   - encoding: a subsequence (n_j) and convergence ν^{n_j} → ν (Assumption 2.1 (2)) → φ : ℕ → ℕ with StrictMono φ and Tendsto (ν ∘ φ) atTop (𝓝 ν) in the topology of E; reason: the standard encoding of subsequences and convergence
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.2, Lemma 2.4 b), p.6

import Mathlib
import Definitions.Def_SubmodMFG_DedekindSuperComplete
import Definitions.Def_SubmodMFG_argminSet
import Definitions.Def_SubmodMFG_bestResponse
import Definitions.Def_SubmodMFG_Assumption21
import Definitions.Def_SubmodMFG_Assumption23

namespace SubmodMFG

/-- **Lemma 2.4 b)** — the infimum and the supremum of the best responses
are monotone in the distribution.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.2, Lemma 2.4 b), p.6: "Under Assumptions 2.1 and 2.3 we have that: b) For all
µ, µ̄ ∈ L with µ ≤^L µ̄, inf R(µ) ≤^L inf R(µ̄) and sup R(µ) ≤^L sup R(µ̄)."

**Formalization Note.** Standing hypotheses of §2 (pp.5–6): `L` is a complete (`CompleteLattice`) and
Dedekind super complete lattice, `E` a topological space, `p : E → L`, and `J : E → L → ℝ`
(curried, `J ν µ = J(ν, µ)`) satisfy Assumptions 2.1 and 2.3. The infimum and supremum are `sInf`/`sSup` in `L`. -/
theorem lemma_2_4_b {E L : Type*} [TopologicalSpace E] [CompleteLattice L] (p : E → L) (J : E → L → ℝ)
    (hL : DedekindSuperComplete L) (h21 : Assumption21 p J) (h23 : Assumption23 p J) :
    ∀ μ μ' : L, μ ≤ μ' →
      sInf (bestResponse p J μ) ≤ sInf (bestResponse p J μ') ∧
        sSup (bestResponse p J μ) ≤ sSup (bestResponse p J μ') := by sorry

end SubmodMFG
