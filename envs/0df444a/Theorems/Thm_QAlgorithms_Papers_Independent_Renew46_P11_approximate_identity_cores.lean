-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_approximate_identity_cores
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.approximate_identity_cores
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:07:51.436709+00:00
-- url     : https://prove2.me/theorems/ebfdae72-7c4e-4e0e-9ce3-ea3943e665ee
-- title:
--   Strong approximate identities give cores and a closed product formula
-- statement:
--   Let $(E,F,\Phi)$ be a proper abstract functional calculus on a complex Banach space $X$, extended by regularisation, and let $F_r,F_b$ denote its regularisable and bounded symbol classes.
--
--   1. If $f\in F_r$, $D$ is a complex linear subspace of $\operatorname{dom}\Phi(f)$, and a sequence $e_n\in F_b$ satisfies $\Phi(e_n)x\to x$ for every $x\in X$ and $\operatorname{ran}\Phi(e_n)\subseteq D$, then $D$ is a core for $\Phi(f)$: the restricted graph is dense in its full graph.
--   2. If $f,g\in F_r$ have sequences $e_n\in\operatorname{Reg}(f)$ and $d_n\in\operatorname{Reg}(g)$, with $e_nf,d_ng\in F_b$, and $\Phi(e_n)\Phi(d_n)=\Phi(e_nd_n)\to I$ strongly, then
--
--   $$\overline{\Phi(f)\Phi(g)}=\Phi(fg).$$
--
--   The closure is taken in $X\times X$. These two assertions give a common core method and a weak product formula, without claiming that the initial product is closed.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 5, Proposition 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ContDiff NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P11

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore restrictGraph)

universe u v w

variable {F : Type u} [CommRing F] [Algebra ℂ F]

variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Proposition 2.3(a,b), PDF pp.5–6. Both assertions are retained;
part (b) closes the whole product graph, as the bar on PDF p.5 specifies. -/
theorem approximate_identity_cores [CompleteSpace X] (C : ElementaryCalculus F X) (hC : IsProper C) :
    (∀ (f : F), Regularisable C f → ∀ (D : Submodule ℂ X),
      (D : Set X) ⊆ graphDomain (calculusValue C f) →
      (∃ e : ℕ → F, (∀ n, (Regularisable C (e n) ∧ (e n) ∈ boundedElements (calculusValue C))) ∧
        StrongIdentity (calculusValue C) e ∧
        ∀ n, graphRange (calculusValue C (e n)) ⊆ (D : Set X)) →
      GraphCore (calculusValue C f) (D : Set X)) ∧
    (∀ (f g : F), Regularisable C f → Regularisable C g →
      (∃ e d : ℕ → F,
        (∀ n, IsRegularizer C f (e n) ∧ IsRegularizer C g (d n) ∧
          (Regularisable C (e n * f) ∧ (e n * f) ∈ boundedElements (calculusValue C)) ∧ (Regularisable C (d n * g) ∧ (d n * g) ∈ boundedElements (calculusValue C))) ∧
        (∀ n, graphMul (calculusValue C (e n)) (calculusValue C (d n)) =
          calculusValue C (e n * d n)) ∧
        StrongIdentity (calculusValue C) (fun n => e n * d n)) →
      closure (graphMul (calculusValue C f) (calculusValue C g)) =
        calculusValue C (f * g)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end
