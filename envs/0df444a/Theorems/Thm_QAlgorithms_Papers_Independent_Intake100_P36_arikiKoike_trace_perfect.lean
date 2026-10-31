-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P36_arikiKoike_trace_perfect
-- name    : QAlgorithms.Papers.Independent.Intake100.P36.arikiKoike_trace_perfect
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:56:12.029496+00:00
-- url     : https://prove2.me/theorems/06f5cc3b-d866-46ca-b94d-6917d55b3bc8
-- title:
--   The coordinate trace is symmetric and perfect for unit parameters
-- statement:
--   Let R be a commutative integral domain with identity, let r≥1 and n≥0, let q be a unit of R, and let Q=(Q₁,…,Qᵣ) be an indexed parameter tuple, allowing repeated and zero values. Let H be the Ariki–Koike algebra with the cyclotomic and quadratic polynomial relations equal to zero, and put Lₖ=q^(1−k)Tₖ₋₁⋯T₁T₀T₁⋯Tₖ₋₁. There is an R-linear functional τ:H→R characterized on the monomial basis by
--
--   $$\tau(L_1^{a_1}\cdots L_n^{a_n}T_w)=\begin{cases}1& a_1=\cdots=a_n=0,\ w=1,\\0&\text{otherwise}.\end{cases}$$
--
--   It satisfies τ(xy)=τ(yx) for all x,y∈H. If every Q_s is a unit, then the map
--
--   $$H\longrightarrow\operatorname{Hom}_R(H,R),\quad x\longmapsto(y\mapsto\tau(xy))$$
--
--   is an R-module isomorphism. Thus H, already finite free by Theorem 2.2, is a symmetric algebra; perfectness is over R itself.
-- source:
--   The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras, arXiv:math/0204025v1, PDF p. 14, Proposition 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P36

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P36

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent adjacentPerm nextPosition)

open QAlgorithms.Papers.Independent.Support21.P06 (wordPerm IsReducedWord)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 3.5, PDF pp.13-14: the coordinate trace and its perfect duality.
The trace is specified on the actual monomials; duality is an R-linear equivalence,
not merely injectivity or nonsingularity over a fraction field. -/
theorem arikiKoike_trace_perfect {R : Type*} [CommRing R] [IsDomain R]
    {r n : ℕ} (hr : 1 ≤ r) (q : Rˣ) (Q : Fin r → R) :
    ∃ tau : ArikiKoike q Q n →ₗ[R] R,
      (∀ z : (Fin n → Fin r) × Equiv.Perm (Fin n),
        tau (arikiKoikeMonomial q Q z) = if (∀ i, (z.1 i).val = 0) ∧ z.2 = 1 then 1 else 0) ∧
      (∀ x y, tau (x * y) = tau (y * x)) ∧
      ((∀ s, IsUnit (Q s)) →
        ∃ e : ArikiKoike q Q n ≃ₗ[R] Module.Dual R (ArikiKoike q Q n),
          ∀ x y, e x y = tau (x * y)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P36

end
