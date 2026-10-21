-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_transported_symmetry_selfAdjointness
-- name    : QAlgorithms.Papers.Independent.Next46.P20.transported_symmetry_selfAdjointness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:19:59.683382+00:00
-- url     : https://prove2.me/theorems/445d5c98-1bab-4021-9199-faa8d18a369a
-- title:
--   Symmetry and self-adjointness under window transport
-- statement:
--   Let $n\ge1$ and fix a unit window $\chi$. For a linear, possibly unbounded operator $a:D(a)\subseteq L^2(\mathbb R^n)\to L^2(\mathbb R^n)$, define $A$ on $\mathcal H_\chi$ by $D(A)=T_\chi D(a)$ and $A(T_\chi\psi)=T_\chi a\psi$. Then
--   $$
--   A\text{ is symmetric}\iff a\text{ is symmetric},\qquad
--   A\text{ is self-adjoint}\iff a\text{ is self-adjoint}.
--   $$
--   Symmetry is tested only on the operator domain and requires no density assumption. Self-adjointness includes a dense domain in the respective Hilbert space and equality with the adjoint graph.
--
--   This retains the source's unbounded-operator meaning.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 9, Theorem 2.9

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF p.9, Theorem 2.9: symmetry and self-adjointness of the full transported
unbounded graph. Only self-adjointness includes a density requirement. -/
theorem transported_symmetry_selfAdjointness {n : ℕ} (hn : 0 < n)
    (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1)
    (a : ConfigurationL2 n →ₗ.[ℂ] ConfigurationL2 n) :
    (graphSymmetric (transportGraph chi (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n))) ↔
      graphSymmetric (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n))) ∧
    (graphSelfAdjointOn (windowSpace chi) (transportGraph chi (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n))) ↔
      graphSelfAdjointOn (⊤ : Submodule ℂ (ConfigurationL2 n)) (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
