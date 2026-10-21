-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P25_optimal_parallel_storage
-- name    : QAlgorithms.Papers.Independent.Claimed50.P25.optimal_parallel_storage
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:16:01.165815+00:00
-- url     : https://prove2.me/theorems/15b2a181-ad44-4344-b78e-f577e20f2c89
-- title:
--   Optimal learning storage is attainable with parallel examples
-- statement:
--   Let \(G\) be a compact Hausdorff group with normalized Borel Haar measure \(\mu\), and \(U:G\to\mathrm U(d)\) a continuous finite-dimensional unitary representation in a fixed basis, with \(N,d\ge1\). Every use of the same unknown \(U(g)\) precedes the new input. Compare all deterministic causal learning networks with arbitrary finite memory, encoded by the complete positive trace-recursive comb constraints of Eq. (6).
--
--   There are a fixed unit vector \(\phi\in(\mathbb C^d)^{\otimes N}\otimes(\mathbb C^d)^{\otimes N}\) and a fixed deterministic CPTP retrieval channel \(R\). Define
--
--   $$
--   \phi_g=(U(g)^{\otimes N}\otimes I)\phi,\qquad
--   C_g(\rho)=R(\rho\otimes|\phi_g\rangle\langle\phi_g|).
--   $$
--
--   This single parallel storage and retrieval strategy attains the optimum: for every admissible learning comb \(L\),
--
--   $$
--   F(L)\le \frac1{d^2}\int_G\langle\!\langle U(g)|J(C_g)|U(g)\rangle\!\rangle\,d\mu(g),
--   $$
--
--   where \(J(C_g)\) is the output-first unnormalized Choi matrix. The preparation and retrieval do not depend on \(g\); the auxiliary register is not acted on by the unknown unitary. This is attainability of the best learning fidelity, rather than simulation of every sequential experiment.
-- source:
--   Optimal quantum learning of a unitary transformation, arXiv:0903.0543v2, PDF p. 3, Lemma 1 (Optimality of parallel storage)

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

/-- PDF pp.3-4, Lemma 1: a fixed normalized preparation on H_o tensor H_i
and fixed CPTP retrieval attain the optimum over all delayed causal N-use combs.
This does not assert parallel simulation of every arbitrary sequential experiment. -/
theorem optimal_parallel_storage (N d : ℕ) [NeZero d] (hN : 0 < N)
    (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular] [IsProbabilityMeasure mu]
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hU : ∀ a b, Continuous (fun g => (U g : Matrix (Fin d) (Fin d) ℂ) a b)) :
    ∃ phi : EuclideanSpace ℂ ((Fin N → Fin d) × (Fin N → Fin d)),
      ∃ R : Superop (Fin d × ((Fin N → Fin d) × (Fin N → Fin d))) (Fin d),
        IsState phi ∧ IsChannel R ∧
        ∀ L : Matrix (LearningBasis N d) (LearningBasis N d) ℂ,
          Normalized (learningSignature N d) (N + 2) L →
          combFidelity mu N d (fun g => (U g : Matrix (Fin d) (Fin d) ℂ)) L ≤
            parallelFidelity mu N d (fun g => (U g : Matrix (Fin d) (Fin d) ℂ)) phi R := by sorry

end MainStatements

end QAlgorithms.Papers.Independent.Claimed50.P25

end
