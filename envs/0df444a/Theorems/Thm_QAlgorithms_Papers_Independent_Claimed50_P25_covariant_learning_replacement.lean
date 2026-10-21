-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P25_covariant_learning_replacement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P25.covariant_learning_replacement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:15:11.50975+00:00
-- url     : https://prove2.me/theorems/cc77d16b-38e3-452c-95ad-f4e70d9372aa
-- title:
--   Covariance without loss for a delayed learning comb
-- statement:
--   Let \(G\) be a compact Hausdorff topological group with normalized Borel Haar measure \(\mu\), and let \(U:G\to\mathrm U(d)\) be a continuous representation on a fixed basis, with \(d,N\ge1\). A learning comb is positive and satisfies every recursive trace constraint of Eq. (6), with scalar initial prefix, scalar delay output, and all \(N\) examples before the new input. Its score \(F\) is the Haar-averaged channel fidelity of Eq. (8), normalized by \(d^2\).
--
--   For every such comb \(L\), there is an admissible comb \(L_c\), fixed independently of the two group elements, with \(F(L_c)=F(L)\), such that
--
--   $$
--   [L_c,\ U(g)_{\mathrm{target,out}}\otimes\overline{U(h)}_{\mathrm{target,in}}\otimes\overline{U(g)}_{\mathrm{examples,out}}^{\otimes N}\otimes U(h)_{\mathrm{examples,in}}^{\otimes N}]=0
--   \quad(g,h\in G).
--   $$
--
--   Its storage prefix \(S=L_c^{(N)}\) satisfies the same recursive normalization, \(\operatorname{Tr}_{\mathrm{target,out}}L_c=I_{\mathrm{target,in}}\otimes S\), and
--
--   $$
--   [S,\overline{U(g)}_{\mathrm{examples,out}}^{\otimes N}\otimes U(h)_{\mathrm{examples,in}}^{\otimes N}]=0.
--   $$
--
--   Thus both covariance conditions can be imposed without changing the learning objective. The formalization retains the recursive wire order and places each factor on its source-labelled wire.
-- source:
--   Optimal quantum learning of a unitary transformation, arXiv:0903.0543v2, PDF p. 3, §III A, Eq.(9): covariance without loss for a learning comb

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P25

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P25

open QAlgorithms.Papers.Independent.Dependency50.P26 (Signature Basis Normalized)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.decEq Classical.propDecidable

section MainStatements

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- PDF p.3, Eqs.(9)-(10): an equally good admissible covariant replacement,
including its storage marginal. H_o uses even wire labels as explicitly defined
above Eq.(6) and in Fig.1, correcting the prose typo below Eq.(10). -/
theorem covariant_learning_replacement (N d : ℕ) [NeZero d] (hN : 0 < N)
    (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular] [IsProbabilityMeasure mu]
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hU : ∀ a b, Continuous (fun g => (U g : Matrix (Fin d) (Fin d) ℂ) a b))
    (L : Matrix (LearningBasis N d) (LearningBasis N d) ℂ)
    (hL : Normalized (learningSignature N d) (N + 2) L) :
    ∃ Lc : Matrix (LearningBasis N d) (LearningBasis N d) ℂ,
      Normalized (learningSignature N d) (N + 2) Lc ∧
      combFidelity mu N d (fun g => (U g : Matrix (Fin d) (Fin d) ℂ)) Lc =
        combFidelity mu N d (fun g => (U g : Matrix (Fin d) (Fin d) ℂ)) L ∧
      (∀ g h : G, Lc * learningAction N d (U g) (U h) (N + 2) =
        learningAction N d (U g) (U h) (N + 2) * Lc) ∧
      ∃ S : Matrix (Basis (learningSignature N d) (N + 1))
          (Basis (learningSignature N d) (N + 1)) ℂ,
        Normalized (learningSignature N d) (N + 1) S ∧
        traceLeft Lc = Matrix.kronecker
          (1 : Matrix (Fin ((learningSignature N d).input (N + 1))) _ ℂ) S ∧
        ∀ g h : G, S * learningAction N d (U g) (U h) (N + 1) =
          learningAction N d (U g) (U h) (N + 1) * S := by sorry

end MainStatements

end QAlgorithms.Papers.Independent.Claimed50.P25

end
