-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_unital_closedReachabilityTrichotomy
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.unital_closedReachabilityTrichotomy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:35:13.13399+00:00
-- url     : https://prove2.me/theorems/4eceaee6-8b58-4640-a786-56a16375b362
-- title:
--   Theorem 5.9: Unital reachable-set trichotomy
-- statement:
--   Let a GKSL generator on $\mathbb C^n$, $n\ge2$, be unital, and let $\lambda$ lie in the ordered Weyl chamber. Exactly one of the following mutually exclusive generator regimes applies:
--
--   1. Purely Hamiltonian: $\overline{\operatorname{reach}_C(\lambda)}=\{\lambda\}$.
--   2. Type $(1,\ldots,1)$ or $(2,1,\ldots,1)$, and not purely Hamiltonian:
--
--   $$\overline{\operatorname{reach}_C(\lambda)}\cap\Delta^{n-1}_{\downarrow}=\{\mu\in\Delta^{n-1}_{\downarrow}:\mu\prec\lambda\}.$$
--
--   3. Type strictly coarser than $(2,1,\ldots,1)$ under refinement: the same left side is $\{e/n\}$ when $\lambda=e/n$, and is a proper subset of the displayed majorization set otherwise.
--
--   All reachable sets here are all-time closures. No unstabilizability hypothesis on the initial state is imposed.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 25, Theorem 5.9: Unital reachable-set trichotomy

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.25, Theorem 5.9: Unital reachable-set trichotomy. Type ordering is strict coarsening under refinement, not lexicographic order. Case conditions are mutually exclusive. Flag for moderation: the printed proof invokes a neighborhood disjoint from stab_R without accounting for degenerate initial lambda; the stated theorem retains every initial chamber point. -/
theorem unital_closedReachabilityTrichotomy {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) (hu : unital D)
    (x : Vec n) (hx : x ∈ chamber n) :
    (purelyHamiltonian D ∧ closure (reachC D x) = {x}) ∨
    (¬purelyHamiltonian D ∧ smallType D ∧
      closure (reachC D x) ∩ chamber n = {y | y ∈ chamber n ∧ majorizedBy y x}) ∨
    ((∃ tau, hasType (relaxationAlgebra D.jump) tau ∧
      refines (2 ::ₘ Multiset.replicate (n - 2) 1) tau ∧
      ¬refines tau (2 ::ₘ Multiset.replicate (n - 2) 1)) ∧
      (if x = barycenter n then closure (reachC D x) ∩ chamber n = {barycenter n}
       else closure (reachC D x) ∩ chamber n ⊂ {y | y ∈ chamber n ∧ majorizedBy y x})) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
