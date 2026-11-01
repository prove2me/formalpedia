-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P81_local_unitary_factorization
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P81.local_unitary_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:59:44.385751+00:00
-- url     : https://prove2.me/theorems/12873a4e-aaf2-4194-ba2e-6cbb29f372e7
-- title:
--   Local conjugation forces a tensor product of unitaries
-- statement:
--   Let $n\ge1$ and let $\mathcal H_i$ be nonzero finite-dimensional complex Hilbert spaces. Let $U$ be unitary on $\bigotimes_{i=1}^n\mathcal H_i$. Suppose that $U^\dagger O_iU$ is supported on factor $i$ whenever $O_i$ is supported on that factor. Then there are factor unitaries $U_i$ such that
--
--   $$U=\bigotimes_{i=1}^n U_i.$$
--
--   For every subset $R$ of the sites, there is a unitary $U_R$ whose conjugation agrees with that of $U$ on every operator supported in $R$ and fixes every operator supported in its complement. This gives the lattice splittability consequence. The factors have arbitrary positive dimensions, and equality includes the scalar phase.
-- source:
--   Symmetries in quantum field theory and quantum gravity, arXiv:1810.05338v2, PDF p. 23, Theorem 2.1: local unitary factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P81

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P81

open scoped BigOperators ComplexConjugate Manifold ContDiff

/-- Theorem 2.1, PDF p.23, proof pp.146--148, lattice consequence p.24.
The finite family is nonempty and its factors are nonzero. Scalar phase is absorbed
in a factor; no qubit restriction and no equality merely up to phase is imposed. -/
theorem local_unitary_factorization {n : ℕ} (hn : 0 < n) (dim : Fin n → ℕ)
    (hdim : ∀ i, 0 < dim i) (U : Matrix.unitaryGroup (FactorBasisIndex dim) ℂ)
    (hlocal : ∀ i (O : Matrix (Fin (dim i)) (Fin (dim i)) ℂ),
      ∃ P : Matrix (Fin (dim i)) (Fin (dim i)) ℂ,
        (star (U : Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ)) *
          embedSite dim i O * (U : Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ) =
            embedSite dim i P) :
    (∃ V : (i : Fin n) → Matrix.unitaryGroup (Fin (dim i)) ℂ,
      (U : Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ) =
        factorTensorMatrix dim (fun i => (V i : Matrix (Fin (dim i)) (Fin (dim i)) ℂ))) ∧
    (∀ s : Finset (Fin n), ∃ V : Matrix.unitaryGroup (FactorBasisIndex dim) ℂ,
      (∀ O : Matrix (RegionIndex dim s) (RegionIndex dim s) ℂ,
        star (V : Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ) * embedRegion dim s O *
          (V : Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ) =
        star (U : Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ) * embedRegion dim s O *
          (U : Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ)) ∧
      (∀ O : Matrix (RegionIndex dim sᶜ) (RegionIndex dim sᶜ) ℂ,
        star (V : Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ) * embedRegion dim sᶜ O *
          (V : Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ) = embedRegion dim sᶜ O)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P81

end
