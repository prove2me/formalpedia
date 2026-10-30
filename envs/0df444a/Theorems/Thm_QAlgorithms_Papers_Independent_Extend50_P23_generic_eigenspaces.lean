-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P23_generic_eigenspaces
-- name    : QAlgorithms.Papers.Independent.Extend50.P23.generic_eigenspaces
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:41:39.518848+00:00
-- url     : https://prove2.me/theorems/5cbe9f28-2a37-40e2-aecd-77b4077aaa4f
-- title:
--   Simple disjoint multiplicity spectra yield the complete irreducible eigenspace decomposition
-- statement:
--   Let $G$ be a compact Hausdorff topological group and $\rho:G\to U(n)$ a continuous representation. Fix an isotypic decomposition independently of $X$: positive dimensions $D_i$ and multiplicities $M_i$, pairwise inequivalent continuous irreducible unitary representations $\sigma_i:G\to U(D_i)$, and a rectangular unitary coordinate map $U$ with
--
--   $$U\rho(g)U^\dagger=\bigoplus_i(I_{M_i}\otimes\sigma_i(g))\qquad(g\in G).$$
--
--   Let $X$ be any Hermitian matrix commuting with $\rho$. Define its multiplicity block $\Xi_i$ by taking the entries of $UXU^\dagger$ with both irreducible coordinates equal to the first coordinate in block $i$; these are computed from $X$ and $U$, rather than supplied as independent matrices. Assume every eigenspace of each $\Xi_i$ has complex dimension at most one and distinct blocks have no eigenvalue in common. Since the extracted blocks are Hermitian, this is precisely the source's simple and disjoint multiplicity-block spectra assumption.
--
--   There exist real numbers $\lambda_{i,a}$, $1\le a\le M_i$, all distinct across pairs $(i,a)$, which exhaust the eigenvalues of each $\Xi_i$ and of $X$. The eigenspaces
--
--   $$E_{i,a}=\ker(X-\lambda_{i,a}I)$$
--
--   span $\mathbb C^n$. Each $E_{i,a}$ is a nonzero irreducible invariant subspace of complex dimension $D_i$ and has an orthonormal row basis $B_{i,a}$. For every such basis, $g\mapsto B_{i,a}\rho(g)B_{i,a}^\dagger$ is a continuous unitary irreducible representation equivalent to $\sigma_i$.
--
--   Thus isotypic component $i$ supplies exactly $M_i$ irreducible eigenspaces of dimension $D_i$. Full-matrix eigenvalues can repeat $D_i$ times; zero is an allowed eigenvalue. When $n=0$, the isotypic index is empty and the span is the zero-dimensional whole space. No numerical eigensolver, accuracy, or runtime guarantee is asserted.
-- source:
--   RepLAB: a computational/numerical approach to representation theory, arXiv:1911.09154v1, PDF p. 5, §2.2, Eq.(10), with Eqs.(6)–(7) on p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P23

open MeasureTheory

open scoped ComplexConjugate BigOperators Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Support21.P09 (EquivalentModels)

open QAlgorithms.Papers.Independent.Dependency50.P05 (UnitaryBetween)

/-- PDF pp.3,5, Eqs.(6),(7),(10): a Hermitian commutant matrix with simple,
disjoint multiplicity-block spectra has irreducible eigenspaces. The Eq.(6)
isotypic basis is fixed independently of X; the blocks are extracted from X.
An eigenbasis splitting rho into irreducible copies is a conclusion, never a
hypothesis. Every isotypic component supplies mult i eigenspaces of dimension
deg i, and every orthonormal row basis of one gives Eq.(10). -/
theorem generic_eigenspaces {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] {n k : ℕ}
    (rho : G → Matrix (Fin n) (Fin n) ℂ) (hrho : IsUnitaryRepresentation rho)
    (deg mult : Fin k → ℕ) (hdeg : ∀ i, 0 < deg i) (hmult : ∀ i, 0 < mult i)
    (sigma : (i : Fin k) → G → Matrix (Fin (deg i)) (Fin (deg i)) ℂ)
    (hsigma : ∀ i, IsUnitaryRepresentation (sigma i) ∧
      QAlgorithms.Papers.Independent.Support21.P09.Irreducible (sigma i))
    (hinequivalent : ∀ i j, i ≠ j → ¬ EquivalentModels (sigma i) (sigma j))
    (U : Matrix (QAlgorithms.Papers.Independent.Support21.P09.BlockIndex mult deg) (Fin n) ℂ)
    (hU : UnitaryBetween U)
    (hdecomp : ∀ g, U * rho g * U.conjTranspose =
      QAlgorithms.Papers.Independent.Support21.P09.irreducibleBlockAction deg mult sigma g)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) (hcommutes : Commutes rho X)
    (hsimple : ∀ (i : Fin k) (z : ℂ),
      Module.finrank ℂ (eigenSpace (multiplicityBlock deg mult hdeg U X i) z) ≤ 1)
    (hdisjoint : ∀ (i j : Fin k), i ≠ j → ∀ z : ℂ,
      eigenSpace (multiplicityBlock deg mult hdeg U X i) z = ⊥ ∨
      eigenSpace (multiplicityBlock deg mult hdeg U X j) z = ⊥) :
    ∃ lambda : (i : Fin k) → Fin (mult i) → ℝ,
      Function.Injective (fun a : Σ i : Fin k, Fin (mult i) => lambda a.1 a.2) ∧
      (∀ (i : Fin k) (z : ℂ),
        eigenSpace (multiplicityBlock deg mult hdeg U X i) z ≠ ⊥ ↔
          ∃ a : Fin (mult i), z = (lambda i a : ℂ)) ∧
      (∀ z : ℂ, eigenSpace X z ≠ ⊥ ↔
        ∃ (i : Fin k) (a : Fin (mult i)), z = (lambda i a : ℂ)) ∧
      (⨆ (i : Fin k) (a : Fin (mult i)), eigenSpace X (lambda i a : ℂ)) = ⊤ ∧
      (∀ (i : Fin k) (a : Fin (mult i)),
        IrreducibleOn rho (eigenSpace X (lambda i a : ℂ)) ∧
        Module.finrank ℂ (eigenSpace X (lambda i a : ℂ)) = deg i ∧
        (∃ B : Matrix (Fin (deg i)) (Fin n) ℂ,
          B * B.conjTranspose = 1 ∧
          LinearMap.range (Matrix.toLin' B.conjTranspose) = eigenSpace X (lambda i a : ℂ)) ∧
        (∀ B : Matrix (Fin (deg i)) (Fin n) ℂ,
          B * B.conjTranspose = 1 →
          LinearMap.range (Matrix.toLin' B.conjTranspose) = eigenSpace X (lambda i a : ℂ) →
          IsUnitaryRepresentation (rowCompression rho B) ∧
          QAlgorithms.Papers.Independent.Support21.P09.Irreducible (rowCompression rho B) ∧
          EquivalentModels (rowCompression rho B) (sigma i))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P23

end
