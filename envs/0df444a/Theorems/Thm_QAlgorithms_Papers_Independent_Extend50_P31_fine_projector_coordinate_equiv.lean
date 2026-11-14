-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_projector_coordinate_equiv
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.fine_projector_coordinate_equiv
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-14T05:46:03.54425+00:00
-- url     : https://prove2.me/theorems/b1e33db4-ff37-4101-9d90-6a53bfd4ea22
-- title:
--   A simultaneous coordinate isomorphism for all fine quantum-channel projectors
-- statement:
--   Under the finite-group unitary and multiplicity-free decomposition assumptions of the paper, let $R=\{(a,i):a\in\Theta,\ 0\le i<d_a\}$ index the fine sectors. There is a complex-linear isomorphism
--
--   $$C:\mathbb C^{n\times n}\longrightarrow\mathbb C^R$$
--
--   such that every fine projector $Q_r$ becomes a single coordinate projection:
--
--   $$C(Q_rv)=e_r\,C(v)_r\qquad(r\in R).$$
--
--   Here the input is row-vectorized, as in the source. The isomorphism is obtained from the given representation intertwiner; the coordinate-projection identity is a theorem, not a field of the input data. It simultaneously controls orthogonality, ranks, and completeness of all fine sectors.
-- source:
--   Mozrzymas, Studzinski and Datta, Structure of irreducibly covariant quantum channels for finite groups, https://arxiv.org/abs/1610.05657v2, PDF pp.10–12, decomposition Eq.(47), Schur orthogonality Eq.(43), and fine projectors in Proposition 17 Eqs.(56)–(57).

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open scoped Matrix ComplexConjugate

theorem QAlgorithms.Papers.Independent.Extend50.P31.fine_projector_coordinate_equiv {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ} (D : Data G A n) :
    ∃ C : ((Fin n × Fin n) → ℂ) ≃ₗ[ℂ] (Row D → ℂ),
      ∀ (r : Row D) (v : (Fin n × Fin n) → ℂ),
        C ((fineMatrix D.U D.F r.1.val r.2).mulVec v) = Pi.single r (C v r) := by sorry
