-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_inverse_sequence
-- name    : SKAlgorithm.Qudit.inverse_sequence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:53.466779+00:00
-- url     : https://prove2.me/theorems/e5d3917c-3396-4502-b017-f58966f3f093
-- title:
--   p. 3 — reversing and inverting an ε-approximating sequence gives an ε-approximation to U†
-- statement:
--   Let $\mathcal G \subseteq SU(d)$ be a finite set of gates closed under $g \mapsto g^\dagger$, and let $S = g_1, \dots, g_m$ be a sequence of gates from $\mathcal G$ that is an $\epsilon$-approximation to a gate $U \in SU(d)$, i.e. $d(U, S) < \epsilon$. Then the inverse sequence $S^\dagger = g_m^\dagger, \dots, g_1^\dagger$ consists of gates from $\mathcal G$, and
--   $$d(U^\dagger, S^\dagger) < \epsilon.$$
--
--   This is the reason Definition 1 requires an instruction set to be closed under adjoints: the recursion of the Solovay-Kitaev algorithm needs approximations to $V^\dagger$ and $W^\dagger$ given approximations to $V$ and $W$.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 3, §2, 'the easily-verified fact that if we have an instruction sequence providing an ǫ-approximation to some unitary U …'

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem inverse_sequence {d : ℕ} (G : Finset (SU d)) (hG : ∀ g ∈ G, g⁻¹ ∈ G)
    (U : SU d) (S : List (SU d)) (hS : ∀ g ∈ S, g ∈ G) (ε : ℝ)
    (hU : opDist U (seqUnitary S) < ε) :
    (∀ g ∈ invSeq S, g ∈ G) ∧ opDist U⁻¹ (seqUnitary (invSeq S)) < ε := by sorry

end SKAlgorithm.Qudit
