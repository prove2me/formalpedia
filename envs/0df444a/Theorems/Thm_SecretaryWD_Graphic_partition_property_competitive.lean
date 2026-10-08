-- Prove2me | Theorems.Thm_SecretaryWD_Graphic_partition_property_competitive
-- name    : SecretaryWD.Graphic.partition_property_competitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:27:52.883978+00:00
-- url     : https://prove2.me/theorems/6aba40b3-7b31-495d-befc-2232687f472e
-- title:
--   An α-partition property gives an eα-competitive algorithm (graphic matroids)
-- statement:
--   Let $G$ be a finite simple graph with edge set $E$, let $\alpha\in\mathbb R$, and let $\mu$ be an $\alpha$-partition scheme for the graphic matroid of $G$ (Definition 5.1). Consider the algorithm that draws a partition $P\sim\mu$, lets the edges arrive in a uniformly random order $\pi$, and runs the classical secretary rule on each part. Then for every nonnegative valuation $v$:
--
--   1. for every partition $P$ in the support of $\mu$ and every order $\pi$, the output is a set of edges of $G$ that contains no cycle;
--   2. the algorithm is $e\alpha$-competitive:
--   $$\mathrm{OPT}(G,v)\;\le\; e\,\alpha\cdot \mathbb E_{P\sim\mu}\,\mathbb E_\pi\big[\mathrm{ALG}(P,\pi)\big].$$
--
--   This is the paper's remark after Theorem 5.4 that an $\alpha$-partition property yields an $(e\alpha)$-competitive algorithm for the matroid secretary problem, specialised to graphic matroids.
--
--   **Formalization Note.** The partition is drawn independently of the arrival order. Feasibility (part 1) holds for every outcome, not only in expectation.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 10, Section 5, paragraph after Theorem 5.4

import Mathlib
import Definitions.Def_SecretaryWD_Graphic_PartitionSecretary

namespace SecretaryWD.Graphic
theorem partition_property_competitive {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (μ : PMF (Finset (Finset (Sym2 V)))) (α : ℝ)
    (hμ : IsPartitionScheme G.edgeFinset μ α) (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    (∀ P ∈ μ.support, ∀ π : Equiv.Perm (Fin G.edgeFinset.card),
        partitionSecretaryOutput G.edgeFinset v P π ⊆ G.edgeFinset ∧
          IsAcyclicSet (partitionSecretaryOutput G.edgeFinset v P π)) ∧
      OPT G.edgeFinset v ≤ Real.exp 1 * α * expectedAlgValue G.edgeFinset v μ := by sorry
end SecretaryWD.Graphic
