-- Prove2me | Theorems.Thm_WeilConjectures_exists_linearEquiv_conj_eq_dualTranspose
-- name    : WeilConjectures.exists_linearEquiv_conj_eq_dualTranspose
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T00:29:39.852371+00:00
-- url     : https://prove2.me/theorems/6721538a-4d53-4901-9b82-7eb3903bf09d
-- title:
--   Every Endomorphism Is Similar to Its Dual-Transpose
-- statement:
--   Let $K$ be a field and $V$ a finite-dimensional $K$-vector space. For every $K$-linear endomorphism $B : V \to V$ there exists a dual equivalence $d : V \xrightarrow{\sim} V^*$ such that
--   $$d \circ B \circ d^{-1} = B^*,$$
--   i.e. $d.\mathrm{conj}(B) = B.\mathrm{dualMap}$.
--
--   Equivalently, every square matrix over a field is similar to its transpose (rational canonical form / invariant factors). Transporting a matrix similarity along $\mathtt{Basis.toDualEquiv}$ yields the stated conjugating dual equivalence. This is the remaining linear-algebra ingredient for rebuilding a dual-Frobenius intertwiner from a pure $V$-conjugation.
-- source:
--   Standard linear algebra: every matrix over a field is similar to its transpose (rational canonical form / invariant factors); cf. Hoffman–Kunze, Linear Algebra, Ch. 6; Bourbaki, Algèbre, Ch. VII

import Mathlib

/-- Every endomorphism of a finite-dimensional vector space over a field is similar to its
dual-transpose: there exists `d : V ≃ₗ Module.Dual K V` with `d.conj B = B.dualMap`.

Equivalently (via any finite basis and `Basis.toDualEquiv`), every square matrix over a field is
similar to its transpose. The existence of such a conjugating dual equivalence is the remaining
linear-algebra ingredient for rebuilding a dual-Frobenius intertwiner from a pure `V`-conjugation. -/

theorem WeilConjectures.exists_linearEquiv_conj_eq_dualTranspose
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (B : V →ₗ[K] V) :
    ∃ (d : V ≃ₗ[K] Module.Dual K V),
      d.conj B = B.dualMap := by
  sorry
