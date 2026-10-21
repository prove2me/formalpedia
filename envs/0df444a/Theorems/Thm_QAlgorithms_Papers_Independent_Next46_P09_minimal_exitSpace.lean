-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P09_minimal_exitSpace
-- name    : QAlgorithms.Papers.Independent.Next46.P09.minimal_exitSpace
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:02:08.961986+00:00
-- url     : https://prove2.me/theorems/0ca9d64e-8065-49a8-9126-0586d3aafe97
-- title:
--   Minimal exit space, detection contraction, and graph-norm estimate
-- statement:
--   Let $H$ be a separable complete complex Hilbert space, let $(C_t)_{t\ge0}$ be a strongly continuous contraction semigroup, and let $K:D\to H$ be its actual full right-derivative generator, with domain $D\subseteq H$. There is a complete complex Hilbert space $E$ and a complex linear map $j:D\to E$ with dense range such that
--
--   $$\langle j\psi,j\phi\rangle_E=-\langle K\psi,\phi\rangle_H-\langle\psi,K\phi\rangle_H\qquad(\psi,\phi\in D).$$
--
--   The inner products are conjugate-linear in their first argument. This minimal exit space is unique up to a unitary intertwining the maps $j$. There is a contraction $J:H\to L^2((0,\infty),dt;E)$ whose values satisfy $(J\phi)(t)=jC_t\phi$ almost everywhere for $\phi\in D$, and, for every $\phi\in H$,
--
--   $$\|J\phi\|^2=\|\phi\|^2-\lim_{t\to\infty}\|C_t\phi\|^2\le\|\phi\|^2.$$
--
--   For a finite linear combination $\rho$ of rank-one operators $|\phi\rangle\langle\psi|$ with $\phi,\psi\in D$, define $j^{\rm rank}\rho$ linearly by replacing its two factors with their images under $j$. Let $L^0$ denote the no-event generator, acting on such rank-one operators as $|K\phi\rangle\langle\psi|+|\phi\rangle\langle K\psi|$. Then
--
--   $$\|j^{\rm rank}\rho\|_1\le\|L^0\rho\|_1.$$
--
--   Here $\|\cdot\|_1$ is the trace norm. These statements identify the separated completion in the loss form and the bounded detector map on the entire system space.
-- source:
--   Unbounded generators of dynamical semigroups, arXiv:1707.02266v1, PDF p. 5, Section II.B, minimal exit space and bounded detection map

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P09

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P09

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass IsTraceClass traceNormValue operatorTrace IsPositive)

open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

/-- Section II.B, arXiv:1707.02266v1, PDF pp.5,7, (6),(7),(10).
Uniqueness is up to an intertwining unitary. The norm identity is for the exact
loss form, with derivative at t=0. The last clause is the full finite-rank
trace-norm estimate; it is not restricted to positive operators. -/
theorem minimal_exitSpace [TopologicalSpace.SeparableSpace H]
    (C : ContractionSemigroup H) (D : Submodule ℂ H) (K : D →ₗ[ℂ] H)
    (hGenerator : IsHilbertGenerator C D K) :
    ∃ E : MinimalExitSpace D K,
      (∀ F : MinimalExitSpace D K,
        ∃ U : E.carrier ≃ₗᵢ[ℂ] F.carrier, ∀ x : D, U (E.j x) = F.j x) ∧
      (∃ J : H →L[ℂ] Lp E.carrier 2 (volume.restrict (Set.Ioi (0 : ℝ))),
        (∀ x : H, ‖J x‖ ≤ ‖x‖) ∧
        (∀ x : D, ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ∃ y : D, (y : H) = C.maps t.toNNReal (x : H) ∧
            (J (x : H)) t = E.j y) ∧
        (∀ x : H, Tendsto (fun t : NNReal => ‖C.maps t x‖ ^ 2) atTop
          (nhds (‖x‖ ^ 2 - ‖J x‖ ^ 2)))) ∧
      (∀ (n : ℕ) (r : Fin n → ℂ) (phi psi : Fin n → D),
        traceNormValue (∑ i, r i • InnerProductSpace.rankOne ℂ (E.j (phi i)) (E.j (psi i))) ≤
          traceNormValue (∑ i, r i •
            (InnerProductSpace.rankOne ℂ (K (phi i)) (psi i : H) +
             InnerProductSpace.rankOne ℂ (phi i : H) (K (psi i))))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P09

end
