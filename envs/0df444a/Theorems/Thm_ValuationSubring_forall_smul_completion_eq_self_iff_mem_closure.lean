-- Prove2me | Theorems.Thm_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure
-- name    : ValuationSubring.forall_smul_completion_eq_self_iff_mem_closure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/1cbdb6a0-8cf5-5d32-8de9-87119ea07ca1
-- title:
--   Ax–Sen–Tate: invariants in ℂₚ of a subgroup
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ satisfying `LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb Q}$ lies in the set of nonunits of $A$ (so $A$ is a valuation ring of residue characteristic $p$). Let $A$.`decompositionSubgroup ℚ` be the subgroup of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of automorphisms preserving $A$, let $H$ be an arbitrary subgroup of it, and let $x$ be an element of the completion $C$ of $\overline{\mathbb Q}$ with respect to the valuation of $A$, on which the decomposition group acts by the scalar action coming from its action by isometries. The assertion is an equivalence: $\sigma \bullet x = x$ for every $\sigma$ in the decomposition group lying in $H$, if and only if $x$ belongs to the topological closure in $C$ of the image, under the canonical map $\overline{\mathbb Q} \to C$, of the fixed field in $\overline{\mathbb Q}$ of the subgroup of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ obtained by pushing $H$ forward along the inclusion of the decomposition group. No closedness hypothesis on $H$ is imposed.
--
--   This is the Ax–Sen–Tate theorem in the form computing, for an arbitrary subgroup $H$ of a decomposition group, the $H$-invariants of $\mathbb{C}_p$ as the closure of the fixed field $\overline{\mathbb Q}^H$. It is used, with $H$ taken to be an inertia subgroup, in the analysis of valuations of elements fixed by inertia, via [`ValuationSubring.exists_valuation_eq_zpow_and_exists_pow_eq_of_forall_inertia_smul_completion_eq`](thm.html#ValuationSubring.exists_valuation_eq_zpow_and_exists_pow_eq_of_forall_inertia_smul_completion_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ValuationSubring_CompletionDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.forall_smul_completion_eq_self_iff_mem_closure
    (p : ℕ) (hp : p.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (H : Subgroup ↥(A.decompositionSubgroup ℚ)) (x : A.valuation.Completion) :
    (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ H → σ • x = x) ↔
      x ∈ closure (((↑) : AlgebraicClosure ℚ → A.valuation.Completion) ''
        (IntermediateField.fixedField (H.map (A.decompositionSubgroup ℚ).subtype) :
          Set (AlgebraicClosure ℚ))) := by sorry
