-- Prove2me | Theorems.Thm_WeingartenCalc_Fundamental_projection_onto_invariants
-- name    : WeingartenCalc.Fundamental.projection_onto_invariants
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:56.739615+00:00
-- url     : https://prove2.me/theorems/5d8f3fb8-410c-4acd-8093-7ebda0a26633
-- title:
--   Section 2, p. 4 — the Haar average $P$ is the selfadjoint idempotent onto the invariant tensors $(H^{\otimes d})^G$
-- statement:
--   Let $G$ be a compact Hausdorff topological group with its Haar probability measure $\mu$, let $U : G\to\mathrm{U}(N)$ be a continuous unitary representation on $H=\mathbb{C}^N$, fix $d\in\mathbb{N}$, and let
--
--   $$P=\int_G U^{\otimes d}(g)\,d\mu(g)$$
--
--   be the Haar average of the tensor-power matrices on $H^{\otimes d}$. Then:
--
--   1. $P$ is selfadjoint: $P^*=P$;
--   2. $P$ is idempotent: $P^2=P$;
--   3. the image of $P$ is the space of $G$-invariant tensors,
--   $$\operatorname{im}P=(H^{\otimes d})^G=\{t\in H^{\otimes d} : U^{\otimes d}(g)\,t=t\ \text{for all } g\in G\}.$$
--
--   Together, $P$ is the orthogonal projection of $H^{\otimes d}$ onto $(H^{\otimes d})^G$. This is what reduces the computation of Weingarten integrals to the invariant theory of $G$: once a basis of the invariant tensors is known, $P$ is determined by linear algebra.
--
--   **Formalization Note** $P^*$ is the conjugate transpose `Pᴴ`; the image is the range of the linear map $t\mapsto Pt$ on `(Fin d → Fin N) → ℂ`; the invariant subspace is defined from the representation itself.
-- source:
--   Collins, Matsumoto & Novak, The Weingarten Calculus, arXiv:2109.14890v1, p. 4, Section 2 ("Thus P is a selfadjoint idempotent, and as such P orthogonally projects H⊗d onto its image, which is the space of G-invariant tensors")

import Mathlib
import Definitions.Def_WeingartenCalc_Fundamental_TensorPower

open MeasureTheory Matrix

namespace WeingartenCalc.Fundamental

theorem projection_onto_invariants
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ) :
    (averagingOperator μ U d)ᴴ = averagingOperator μ U d ∧
      averagingOperator μ U d * averagingOperator μ U d = averagingOperator μ U d ∧
      LinearMap.range (averagingOperator μ U d).mulVecLin = invariants U d := by sorry

end WeingartenCalc.Fundamental
