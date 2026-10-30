-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_abelian_zero_trace_obstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.abelian_zero_trace_obstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:06:27.325577+00:00
-- url     : https://prove2.me/theorems/2cbb0d33-9d88-4459-99de-4e1a03edf7f4
-- title:
--   Corollary 5: zero on-site trace obstructs Abelian universality
-- statement:
--   Let G be Abelian, let n identical positive-dimensional sites carry the same unitary representation u, and let 1≤k<n. If Tr(u(g))=0 for some g∈G, then
--
--   $$\dim_{\mathbb R}h_k<\dim_{\mathbb R}h_n.$$
--
--   The invariant Lie algebras are those of the physical tensor product representation. Thus a zero local character value obstructs universality at every strictly smaller locality.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 20, Corollary 5: a zero on-site trace obstructs Abelian universality

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.20, Corollary 5: the zero-trace obstruction for Abelian symmetries.
Identical local actions are explicit, and the conclusion uses the actual real
Lie algebras rather than assuming any irrep counting formula. -/
theorem abelian_zero_trace_obstruction {G A : Type*} [CommGroup G]
    [Fintype A] [DecidableEq A] [Nonempty A] (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k < n) (r : OnSite G (fun _ : Fin n => A))
    (hSame : ∀ i j g, r.u i g = r.u j g)
    (hZero : ∃ (j : Fin n) (g : G), Matrix.trace (r.u j g) = 0) :
    Module.finrank ℝ (symmetricLocalLie r.total k) < Module.finrank ℝ (symmetricLocalLie r.total n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
