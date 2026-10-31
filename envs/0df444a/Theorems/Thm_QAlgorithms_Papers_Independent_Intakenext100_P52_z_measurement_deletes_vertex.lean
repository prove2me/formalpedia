-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_z_measurement_deletes_vertex
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.z_measurement_deletes_vertex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:43:00.357215+00:00
-- url     : https://prove2.me/theorems/37265998-cecd-4806-8d9f-8903cbc303bc
-- title:
--   §5.1: Z measurement deletes a cluster vertex
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, with every edge oriented once for its coordinate representation, and let $|C_G\rangle$ be its normalized cluster state. For $A\in V$ and computational outcome $s\in\{0,1\}$, identify the surviving wires with $V\setminus\{A\}$. The destructive $Z_A$ branch satisfies
--
--   $$ (\langle s|_A\otimes I)|C_G\rangle=\frac1{\sqrt2}\left(\prod_{v\sim A}Z_v^s\right)|C_{G-A}\rangle,\qquad\Pr(s)=\frac12. $$
--
--   The measured wire is removed by an explicit insertion bijection on bit strings. Isolated vertices and singleton graphs are included by the empty-product convention. The intermediate normalization factor omitted on p.12 is retained.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 12, §5.1: Z measurement deletes a cluster vertex

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Z deletion, PDF pp.11–12: includes the missing intermediate 1/sqrt(2)
factor and explicitly removes the measured register. Singleton and isolated
vertices are allowed; their neighbour product is empty. -/
theorem z_measurement_deletes_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (hloop : ∀ e ∈ E, e.1 ≠ e.2)
    (horient : ∀ e ∈ E, (e.2,e.1) ∉ E) (A : V) (s : Bool) :
    let b : Vec ({v : V // v ≠ A} → Bool) :=
      WithLp.toLp 2 fun z => graphClusterState E (insertSite A s z)
    b = ((Real.sqrt 2)⁻¹ : ℂ) •
      (WithLp.toLp 2 fun z => neighbourPhase E A s z * graphClusterState (deletedEdges E A) z) ∧
    ‖b‖ ^ 2 = (1 / 2 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
