-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_appendix_svd
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.appendix_svd
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:26:15.256977+00:00
-- url     : https://prove2.me/theorems/571b7522-68fc-436d-afbc-f3bb8a0767e4
-- title:
--   §VII, Eqs.(20)–(23): state-adapted decomposition
-- statement:
--   Let $\psi$ be any vector in a separable isotypic block with complete coherent basis $\{e_n^{(\mu)}\}$. Its coefficient matrix is Hilbert-Schmidt. There exist unitaries $V$ on multiplicity space and $U$ on component coordinates, a complete coherent basis
--
--   $$g_k^{(\mu)}=\sum_{\nu,n}V_{\mu\nu}U_{kn}e_n^{(\nu)},$$
--
--   and nonnegative singular coefficients $\sigma_\mu$ such that $\psi=\sum_\mu\sigma_\mu g_{j(\mu)}^{(\mu)}$ in Hilbert norm. Each occupied row has one direction $j(\mu)$, and these directions are distinct across occupied rows; null-space directions remain part of the complete basis. Moreover $\sum_\mu\sigma_\mu^2=\|\psi\|^2$. The new closed row spaces are exhaustive invariant equivalent irreducible components, and distinct projected components are orthogonal after coherent identification. This gives an adapted decomposition for every input, not an assumption on the original decomposition.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 7, §VII, Eqs.(20)–(23): state-adapted decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P30

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39 (IsTraceClass)

open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)

open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)

open scoped ComplexConjugate ComplexOrder Manifold ContDiff ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (R : CovariantHilbertData G H)

variable {M : Type*} [DecidableEq M]

variable (D : Components R M)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet displacement displacementMatrix coherentMeasure coherentKet)

variable {J : Type*} [DecidableEq J]

/-- PDF p.8, Eqs.(20)–(23): Schmidt/SVD-adapted exhaustive decomposition.
Partial matching retains unmatched null-space basis vectors at infinite dimension;
only distinct occupied rows are required to have different singular directions. -/
theorem appendix_svd [Countable M] [Countable J] [Nonempty M] [Nonempty J]
    (hLie : RealLie G) (b : HilbertBasis (M × J) ℂ H) (hb : Isotypic R b) (psi : H) :
    Summable (fun p : M × J => ‖inner ℂ (b p) psi‖ ^ 2) ∧
    ∃ (V : lp (fun _ : M => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : M => ℂ) 2)
      (U : lp (fun _ : J => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : J => ℂ) 2)
      (bnew : HilbertBasis (M × J) ℂ H) (sigma : M → ℝ) (matching : M → Option J),
      Isotypic R bnew ∧ (∀ i, 0 ≤ sigma i) ∧
      (∀ i, matching i = none ↔ sigma i = 0) ∧
      (∀ i j k, matching i = some k → matching j = some k → i = j) ∧
      (∀ i k, HasSum (fun p : M × J =>
        (unitaryEntry V i p.1 * unitaryEntry U k p.2) • b p) (bnew (i, k))) ∧
      (∀ i k, inner ℂ (bnew (i, k)) psi = if matching i = some k then (sigma i : ℂ) else 0) ∧
      HasSum (fun i => match matching i with
        | none => 0
        | some k => (sigma i : ℂ) • bnew (i, k)) psi ∧
      Summable (fun i => sigma i ^ 2) ∧ (∑' i, sigma i ^ 2) = ‖psi‖ ^ 2 ∧
      (∀ i j, i ≠ j →
        inner ℂ (∑' k, inner ℂ (bnew (i, k)) psi • bnew (i, k))
          (rowTransport bnew i j (∑' k, inner ℂ (bnew (j, k)) psi • bnew (j, k))) = 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
