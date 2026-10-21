-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_relative_entropy_bound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.relative_entropy_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:21:51.75241+00:00
-- url     : https://prove2.me/theorems/0ad6b985-070f-4354-8f69-5bc3c93c52e4
-- title:
--   Remark 3: relative entropy dominates spectral inf-divergence
-- statement:
--   Let $\rho_n,\sigma_n$ be arbitrary normalized density operators on arbitrary complex Hilbert spaces $H_n$. Let $D(\rho_n\|\sigma_n)$ denote Umegaki relative entropy in nats, retaining infinity and without subtracting infinite entropies. For any allowed likelihood family, define the spectral inf-divergence $D_L=\sup\{a:\limsup_n\rho_n[I-S_n(a)]\le0\}$.
--
--
--   $$
--   \liminf_{n\to\infty}\frac{1}{n}D(\rho_n\|\sigma_n)\ge D_L.
--   $$
--
--   This compares the normalized relative-entropy rate with the spectral inf-divergence.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 9, Remark 3: relative entropy dominates spectral inf-divergence

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Remark 3, PDF p.9: arbitrary normalized quantum states; relative entropy is
reused from accepted P13's extended finite-projection definition, in nats.
No finite dimension, finite entropy, or common state space is assumed. -/
theorem relative_entropy_bound (Q : ℕ → QuantumData.{u})
    (hrho : ∀ k, QAlgorithms.Papers.Independent.Dependency50.P13.IsTraceClass (Q k).rho)
    (hsigma : ∀ k, QAlgorithms.Papers.Independent.Dependency50.P13.IsTraceClass (Q k).sigma)
    (hnorm : ∀ k, positiveTrace (Q k) (Q k).rho = 1 ∧ positiveTrace (Q k) (Q k).sigma = 1)
    (S : LikelihoodFamily (fun k => SimpleHypothesisSystem.quantum (Q k))) :
    divergenceL S 0 ≤ liminf (fun k => perBlock k
      ((relativeEntropy ⟨(Q k).rho, hrho k⟩ ⟨(Q k).sigma, hsigma k⟩ : ℝ≥0∞) : EReal)) atTop := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
