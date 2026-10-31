-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_local_filter_continuity
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.local_filter_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:17:03.81199+00:00
-- url     : https://prove2.me/theorems/252b6c90-dc92-4460-b47d-46e5e62382bb
-- title:
--   Note [16]: continuity along invertible local filtering of multipartite pure states
-- statement:
--   Fix $m\ge2$ parties with positive finite local dimensions, a unit pure state $\psi$, a selected party $k$, and a local matrix $A$ satisfying $\operatorname{Tr}|A^\dagger A|=1$. Let $E$ be a finite real pure-state functional across these multipartite systems, satisfying condition (9) for actual asymptotic multipartite LOCC conversions. Define
--
--   $$M_1(\epsilon)=\sqrt{I-\epsilon A^\dagger A},\quad p(\epsilon)=\|M_1(\epsilon)\psi\|^2,\quad \psi_\epsilon=\frac{M_1(\epsilon)\psi}{\sqrt{p(\epsilon)}},$$
--
--   where the filter acts only on party $k$. There exist $C>0$ and $0<\epsilon_0<1$, depending on these fixed data, such that for every $0<\epsilon<\epsilon_0$ the vector $\psi_\epsilon$ has norm one and
--
--   $$|1-p(\epsilon)|\le C\epsilon,\qquad \|\psi_\epsilon-\psi\|\le C\epsilon,$$
--
--   $$|E(|\psi\rangle\langle\psi|)-E(|\psi_\epsilon\rangle\langle\psi_\epsilon|)|\le C\epsilon.$$
--
--   The completion $M_2=\sqrt\epsilon A$ is the failure branch. The constants are not uniform over states, operators or dimensions. No continuity across SLOCC classes or bipartite entropy characterization is assumed.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 5, Note [16]: continuity along invertible local filtering of multipartite pure states

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF p.5, reference note [16]: O(epsilon) continuity along the
specified invertible local filter for a fixed normalized multipartite pure
state. Constants are chosen after E, dimensions, psi, party and A; they are
not uniform over those objects. Values refer to normalized pure projectors.
No continuity between different SLOCC classes is asserted. -/
theorem local_filter_continuity
    (m : ℕ) (hm : 2 ≤ m)
    (E : (d : Fin m → ℕ) → MultiOp d → ℝ) (hE : IsMultiAsymptoticMeasure E)
    (d : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (psi : EuclideanSpace ℂ (MultiBasis d)) (hpsi : ‖psi‖ = 1)
    (party : Fin m) (A : Matrix (Fin (d party)) (Fin (d party)) ℂ)
    (hA : traceNorm (Aᴴ * A) = 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 < 1 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
        ‖filterVector d party A psi epsilon‖ = 1 ∧
        |1 - filterProbability d party A psi epsilon| ≤ C * epsilon ∧
        ‖filterVector d party A psi epsilon - psi‖ ≤ C * epsilon ∧
        |E d (pureDensity psi) - E d (pureDensity (filterVector d party A psi epsilon))|
          ≤ C * epsilon := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
