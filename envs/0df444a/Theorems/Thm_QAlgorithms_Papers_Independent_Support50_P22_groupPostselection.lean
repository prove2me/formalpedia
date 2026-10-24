-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P22_groupPostselection
-- name    : QAlgorithms.Papers.Independent.Support50.P22.groupPostselection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:53:25.927502+00:00
-- url     : https://prove2.me/theorems/095b1797-8819-4d8a-92c8-586115ee9337
-- title:
--   Finite or locally compact group postselection
-- statement:
--   Let $G$ be a finite group or a Hausdorff locally compact topological group, and let $U$ be a continuous unitary representation on a nonzero finite-dimensional complex space $V$ (finite groups carry the discrete topology). Give a coordinate copy $W\cong V$ the dual action $U(g^{-1})^T$. Define
--   $$
--   S=(V\otimes W)^G,\qquad m=\dim_{\mathbb C}S,\qquad
--   \tau_{VW}=m^{-1}P_S,\qquad \tau_V=\operatorname{Tr}_W\tau_{VW}.
--   $$
--   Then $m>0$ and both technical results extend as follows. For any fixed normalized purification $\psi_{VR}$ of $\tau_V$ and any complex-linear map $\Delta:\operatorname{End}(V)\to\operatorname{End}(B)$, if for every $g$ there is a CPTP $K_g$ satisfying $\Delta\circ\operatorname{Ad}(U(g))=K_g\circ\Delta$, then
--   $$
--   \|\Delta\|_\diamond\le m\,\|(\Delta\otimes\operatorname{id}_R)(|\psi\rangle\langle\psi|)\|_1.
--   $$
--   Also, for any fixed normalized purification $\Psi_{VWN}$ of $\tau_{VW}$ and any density $\rho$ supported on the fixed vector space $S$, there is an effect $0\preceq M\preceq I_N$ such that
--   $$
--   \rho=m(\operatorname{id}_{VW}\otimes T_M)(|\Psi\rangle\langle\Psi|),\qquad T_M(X)=\operatorname{Tr}(XM).
--   $$
--   This uses the invariant-space dimension in place of the permutation factor; no polynomial bound on $m$ is asserted.
-- source:
--   Post-selection technique for quantum channels with applications to quantum cryptography, arXiv:0809.3019v1, PDF p. 3, Unnumbered group-symmetry extension, concluding remark and footnote 17

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P22

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P18 (ClassicalOutput)

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixBorelSpace

/-- Group extension of BOTH technical results, PDF p.3 concluding remark and
p.4 footnote 17. Finite groups use their discrete topology; for locally
compact groups the finite-dimensional unitary representation is continuous.
The factor is the invariant-space dimension, with no polynomial claim. -/
theorem groupPostselection
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (hG : Finite G ∨ LocallyCompactSpace G)
    (v : ℕ) (hv : 0 < v) (U : G →* Matrix.unitaryGroup (Fin v) ℂ) (hU : Continuous U) :
    let S := invariantSpace U
    let m := Module.finrank ℂ S
    0 < m ∧
    (∀ (R B : Type*) [Fintype R] [DecidableEq R] [Nonempty R]
        [Fintype B] [DecidableEq B] [Nonempty B],
      ∀ psi : EuclideanSpace ℂ (Fin v × R),
      FinitePurification psi (traceRight (groupTau U)) →
      ∀ Delta : Matrix (Fin v) (Fin v) ℂ →ₗ[ℂ] Matrix B B ℂ,
      (∀ g : G, ∃ K : Superop B B, IsChannel K ∧
        ∀ X, Delta (conjSuperop (U g : Matrix (Fin v) (Fin v) ℂ) X) = K (Delta X)) →
      diamond Delta ≤ (m : ℝ) * traceNorm (tensorId Delta (pureDensity psi))) ∧
    (∀ (N : Type*) [Fintype N] [DecidableEq N] [Nonempty N],
      ∀ psi : EuclideanSpace ℂ ((Fin v × Fin v) × N), FinitePurification psi (groupTau U) →
      ∀ rho : Matrix (Fin v × Fin v) (Fin v × Fin v) ℂ,
      IsDensityMatrix rho → RangeSupported rho S →
      ∃ M : Matrix N N ℂ, IsEffect M ∧ rho = (m : ℂ) • postselect M (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P22

end
