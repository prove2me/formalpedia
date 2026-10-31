-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P25_classical_extensions_and_topology
-- name    : QAlgorithms.Papers.Independent.Intake100.P25.classical_extensions_and_topology
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:24:07.197516+00:00
-- url     : https://prove2.me/theorems/d66625ee-6f32-4561-960a-4a7a726be255
-- title:
--   §2, unnumbered [Sal99, AD10]: components, ambient contraction, extensions
-- statement:
--   For $n\ge1$, put $Sp^*=\{A\in\operatorname{Sp}(2n,\Omega_0):\det(A-I)\ne0\}$. It has exactly two connected components, the nonempty sets $P=\{\det(A-I)>0\}$ and $M=\{\det(A-I)<0\}$ inside the symplectic group, containing $W^+=-I$ and $W^-=\operatorname{diag}(2,-1,\ldots,-1,1/2,-1,\ldots,-1)$ respectively. Every loop in $Sp^*$ contracts with its basepoint fixed in the ambient symplectic group. Every continuous $\psi\in SP(n)$ admits an extension $\widetilde\psi:[0,2]\to\operatorname{Sp}(2n,\Omega_0)$ agreeing on $[0,1]$, lying in $Sp^*$ on $[1,2]$, and ending at $W^+$ or $W^-$. For any two such extensions,
--
--   $$\deg(\rho^2\circ\widetilde\psi_1)=\deg(\rho^2\circ\widetilde\psi_2).$$
--
--   Here $\rho$ is Definition 5 spectral rotation. Each composite is continuous, circle-valued, and has value $1$ at both endpoints. This gives the topology, existence and degree independence used in defining the classical index. The contracting homotopy may pass through matrices with eigenvalue $1$.
-- source:
--   Generalized Conley-Zehnder index, arXiv:1307.7239v1, PDF p. 6, §2, unnumbered [Sal99, AD10]

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P25

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Intake100.P25

open QAlgorithms.Papers.Independent.Gap50repair.P01

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

attribute [local instance] Classical.propDecidable

/-- Section 2 [Sal99,AD10], PDF p.6: two components, ambient loop contraction,
extension existence, circle-loop property and degree independence, together. -/
theorem classical_extensions_and_topology {n : ℕ} (hn : 1 ≤ n) :
    let P : Set (GroupedRealMatrix n) := {A | IsSymplectic A ∧ 0 < (A-1).det}
    let M : Set (GroupedRealMatrix n) := {A | IsSymplectic A ∧ (A-1).det < 0}
    IsConnected P ∧ IsConnected M ∧ Disjoint P M ∧
    {A | IsSymplectic A ∧ (A-1).det ≠ 0} = P ∪ M ∧
    wPlus n ∈ P ∧ wMinus n ∈ M ∧
    (∀ S : Set (GroupedRealMatrix n), IsConnected S → S ⊆ P ∪ M → S ⊆ P ∨ S ⊆ M) ∧
    (∀ q : ℝ → GroupedRealMatrix n, IsPath q 1 → q 0 = q 1 →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (q t-1).det ≠ 0) →
      FixedHomotopic q (fun _ => q 0) 1) ∧
    (∀ p : ℝ → GroupedRealMatrix n, IsAdmissible p 1 →
      (∃ e, IsExtension p e) ∧
      (∀ e, IsExtension p e →
        ContinuousOn (fun t => spectralRotation (e t)^2) (Set.Icc (0 : ℝ) 2) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖spectralRotation (e t)^2‖ = 1) ∧
        spectralRotation (e 0)^2 = 1 ∧ spectralRotation (e 2)^2 = 1) ∧
      (∀ e1 e2, IsExtension p e1 → IsExtension p e2 →
        winding (fun t => spectralRotation (e1 t)^2) 2 =
          winding (fun t => spectralRotation (e2 t)^2) 2)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P25

end
