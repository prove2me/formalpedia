-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_appendix_unitary_mixing
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.appendix_unitary_mixing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:24:56.741986+00:00
-- url     : https://prove2.me/theorems/6b0a3db5-1e30-42e7-897d-466f4a7a6776
-- title:
--   §VII: Lemma (Choice of the decomposition into equivalent components)
-- statement:
--   Let an isotypic block of a strongly continuous projective unitary Lie-group representation have a complete coherent orthonormal basis $\{e_k^{(\mu)}\}$, with finite or countable multiplicity and component dimension. Let $V$ be a unitary on the completed multiplicity space. The norm-convergent mixtures
--
--   $$f_k^{(\mu)}=\sum_\nu V_{\mu\nu}e_k^{(\nu)}$$
--
--   form another complete orthonormal basis. Their closed row spans are mutually orthogonal, exhaustive, invariant, and carry equivalent irreducible representations. From any original reference component, the maps $S_{\mu1}=\sum_\nu V_{\mu\nu}I_{\nu1}$ converge on every vector, are isometries onto the new rows, and intertwine the action. Thus unitary mixing preserves the full decomposition even at infinite multiplicity.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 7, §VII: Lemma (Choice of the decomposition into equivalent components)

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

/-- PDF p.8, Lemma: unitary mixing gives complete orthogonal invariant equivalent rows.
S_mu_1 is the norm-convergent displayed sum from the original reference row. -/
theorem appendix_unitary_mixing [Countable M] [Countable J] [Nonempty M] [Nonempty J]
    (hLie : RealLie G) (b : HilbertBasis (M × J) ℂ H) (hb : Isotypic R b)
    (V : lp (fun _ : M => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : M => ℂ) 2) (base : M) :
    ∃ bnew : HilbertBasis (M × J) ℂ H, Isotypic R bnew ∧
      (∀ i k, HasSum (fun j => unitaryEntry V i j • b (j, k)) (bnew (i, k))) ∧
      ∃ S : M → PhysicalOperator H, ∀ i,
        (∀ v, v ∈ closedHilbertRow b base →
          HasSum (fun j => unitaryEntry V i j • rowTransport b j base v) (S i v) ∧
          ‖S i v‖ = ‖v‖ ∧ S i v ∈ closedHilbertRow bnew i) ∧
        (∀ w, w ∈ closedHilbertRow bnew i → ∃ v ∈ closedHilbertRow b base, S i v = w) ∧
        (∀ g v, S i (R.U g v) = R.U g (S i v)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
