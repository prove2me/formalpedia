-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaC_1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaC_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:55:52.756502+00:00
-- url     : https://prove2.me/theorems/0d929ddb-2bc6-49de-9064-74b8ea7ab0eb
-- title:
--   Fixed Specht Bell factors for every symmetric vector
-- statement:
--   Let $D,E$ have the same finite positive dimension $d$, and let $n\ge0$. In compatible Schur–Weyl coordinates, indexed by Young diagrams $\lambda$ of size $n$ with at most $d$ rows, fix the normalized Bell vector $\psi_\lambda$ on the two Specht factors. Both reduced density matrices of $|\psi_\lambda\rangle\langle\psi_\lambda|$ are $\mathrm{id}/\dim V_\lambda$. Every symmetric vector $\Omega\in\operatorname{Sym}^n(D\otimes E)$ has unnormalized Schur coefficients $\phi_\lambda$ satisfying
--
--   $$\Omega=\sum_\lambda\phi_\lambda\otimes\psi_\lambda.$$
--
--   The Bell factors are fixed before $\Omega$. The formal coordinates represent both physical bases by $\mathrm{Fin}(d)$, and use the conjugate transform on $E$ to match the Specht pairings. Synthesis is computed from the accepted constructed Schur transform, rather than assumed as a decomposition property.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 25, Lemma C.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma C.1, Eqs.191–196 (PDF pp.25–26). Physical D,E are both represented
in bases indexed by Fin d. The fixed Bell family is normalized and maximally
entangled; every symmetric input has suitable unnormalized Schur coefficients. -/
theorem lemmaC_1 (d n : ℕ) (hd : 0 < d) :
    (∀ lambda : QAlgorithms.Schur.Partition d n,
      (∑ x, Complex.normSq (spechtBell lambda x)) = 1 ∧
      traceRight (vectorOuterProduct (spechtBell lambda)) =
        ((((Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda) : ℝ)⁻¹ : ℝ) : ℂ) • 1) ∧
      traceLeft (vectorOuterProduct (spechtBell lambda)) =
        ((((Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda) : ℝ)⁻¹ : ℝ) : ℂ) • 1)) ∧
    (∀ omega : ((Fin n → Fin d) × (Fin n → Fin d)) → ℂ,
      (∀ (p : Equiv.Perm (Fin n)) x, omega (x.1 ∘ p,x.2 ∘ p) = omega x) →
      ∃ phi : (lambda : QAlgorithms.Schur.Partition d n) →
        (Fin (Module.finrank ℂ (QAlgorithms.Schur.schurModule lambda)) ×
          Fin (Module.finrank ℂ (QAlgorithms.Schur.schurModule lambda))) → ℂ,
        omega = pairedSchurSynthesis d n phi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
