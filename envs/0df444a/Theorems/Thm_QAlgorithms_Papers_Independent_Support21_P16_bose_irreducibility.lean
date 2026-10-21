-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_bose_irreducibility
-- name    : QAlgorithms.Papers.Independent.Support21.P16.bose_irreducibility
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:38:36.676674+00:00
-- url     : https://prove2.me/theorems/90984f3c-5e3a-4edf-969f-2c7ec023c337
-- title:
--   Irreducibility and the invariant Bose state
-- statement:
--   Let $d>0$ and $n\ge1$ be integers. Let $H_n^+$ be the permutation-fixed subspace of $(\mathbb C^d)^{\otimes n}$, $s_n$ its orthogonal projector, and $D_n=\binom{d+n-1}{n}$. Every $U^{\otimes n}$, for $U\in U(d)$, preserves $H_n^+$. Moreover, for every complex operator $A$,
--   $$
--   A=s_nA=As_n,\quad
--   AU^{\otimes n}=U^{\otimes n}A\ \text{for all }U\in U(d)
--   \quad\Longrightarrow\quad A=c\,s_n\ \text{for some }c\in\mathbb C.
--   $$
--   The operator $\tau_n=s_n/D_n$ is a Bose-supported density matrix. A Bose-supported density matrix $\rho$ is invariant under $\rho\mapsto U^{\otimes n}\rho U^{*\otimes n}$ for all $U\in U(d)$ if and only if $\rho=\tau_n$.
--
--   This states irreducibility by its full commutant characterization and identifies the unique invariant normalized state.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 6, bose-irreducibility

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF p.6: U(d) invariance, the full commutant characterization of
irreducibility, and uniqueness of the invariant Bose density matrix. -/
theorem bose_irreducibility (d n : ℕ) (hd : 0 < d) (hn : 1 ≤ n) :
    (∀ u : UnitaryGroup d, ∀ v ∈ boseSpace d n,
      QAlgorithms.act (QAlgorithms.piKron n (u : Matrix (Fin d) (Fin d) ℂ)) v ∈
        boseSpace d n) ∧
    (∀ A : TensorMat d n, BoseSupported A →
      (∀ u : UnitaryGroup d, A * QAlgorithms.piKron n (u : Matrix (Fin d) (Fin d) ℂ) =
        QAlgorithms.piKron n (u : Matrix (Fin d) (Fin d) ℂ) * A) →
      ∃ c : ℂ, A = c • boseProjector d n) ∧
    QAlgorithms.IsDensityMatrix (boseMixed d n) ∧
    BoseSupported (boseMixed d n) ∧
    (∀ A : TensorMat d n,
      (QAlgorithms.IsDensityMatrix A ∧ BoseSupported A ∧
        ∀ u : UnitaryGroup d,
          QAlgorithms.piKron n (u : Matrix (Fin d) (Fin d) ℂ) * A *
            (QAlgorithms.piKron n (u : Matrix (Fin d) (Fin d) ℂ))ᴴ = A) ↔
      A = boseMixed d n) := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
