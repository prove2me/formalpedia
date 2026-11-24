-- Prove2me | Theorems.Thm_WeilConjectures_exists_dualEquiv_of_conj_eq_smul_symm
-- name    : WeilConjectures.exists_dualEquiv_of_conj_eq_smul_symm
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T00:08:12.979077+00:00
-- url     : https://prove2.me/theorems/9785dce4-31ae-4fb4-ac27-917fe4191132
-- title:
--   Dual-Frobenius Equivalence from $V$-Conjugation $F \sim q F^{-1}$
-- statement:
--   Let $K$ be a field, $V$ a finite-dimensional $K$-vector space, $F : V \xrightarrow{\sim} V$ a $K$-linear automorphism, and $q \in K$. Suppose there exists $g : V \xrightarrow{\sim} V$ with
--   $$g \circ F \circ g^{-1} = q \, F^{-1}.$$
--   Then there exists a dual-Frobenius equivalence $e : V \xrightarrow{\sim} V^*$ such that
--   $$e \circ F \circ e^{-1} = (q \, F^{-1})^*.$$
--
--   This linear-algebra bridge converts a conjugation on $V$ into a conjugating dual intertwiner on $V^*$. Existence uses that every endomorphism is similar to its dual-transpose (equivalently, every matrix over a field is similar to its transpose), transported along a finite-basis dual equivalence $\mathtt{Basis.toDualEquiv}$.
-- source:
--   Standard linear algebra: every matrix over a field is similar to its transpose (rational canonical form / invariant factors); cf. Hoffman–Kunze, Linear Algebra, Ch. 6; Bourbaki, Algèbre, Ch. VII

import Mathlib

/-- If an automorphism `F` is similar to `q • F⁻¹` via some `g : V ≃ₗ[K] V`, then there exists a
dual-Frobenius equivalence `eMid : V ≃ₗ Module.Dual K V` intertwining `F` with `(q • F⁻¹)*`.

This is the linear-algebra bridge from a `V`-conjugation (`g.conj F = q • F.symm`) to a
dual-conjugation (`eMid.conj F = (q • F.symm).dualMap`). The existence uses that every
endomorphism is similar to its dual-transpose (equivalently, every matrix is similar to its
transpose over a field), transported along a finite basis dual equivalence
`Basis.toDualEquiv`. -/

theorem WeilConjectures.exists_dualEquiv_of_conj_eq_smul_symm
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (F : V ≃ₗ[K] V) (q : K) (g : V ≃ₗ[K] V)
    (hg : g.conj (F : V →ₗ[K] V) = (q • (F.symm : V →ₗ[K] V))) :
    ∃ (eMid : V ≃ₗ[K] Module.Dual K V),
      eMid.conj (F : V →ₗ[K] V) = (q • (F.symm : V →ₗ[K] V)).dualMap := by
  sorry
