-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_generalChannelCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.generalChannelCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:23:10.52983+00:00
-- url     : https://prove2.me/theorems/85fdfc4f-925a-452e-9e42-8e2346078b59
-- title:
--   Theorem 1: general quantum-channel coding theorem (seed)
-- statement:
--   Let $\Phi$ be a completely positive trace-preserving map on trace-class operators of a nonzero complex Hilbert space. Let $C_n$ be its maximal $n$-block accessible information, $\bar C_n$ its maximal Holevo information, and $C=\sup_{n\ge1}C_n/n$, $\bar C=\sup_{n\ge1}\bar C_n/n$, allowing infinity. Let $p(n,M)$ be the infimum uniform average error over arbitrary block-state codes and collective positive receiver effects summing to at most the identity. With $M_n=\lceil e^{nR}\rceil$,
--
--   $$C<\infty,\ R>C\ \Longrightarrow\ p(n,M_n)\not\longrightarrow0.$$
--
--   If there is one finite upper bound on $H(\Phi[S])$ for every density $S$, then
--
--   $$R<\bar C\ \Longrightarrow\ p(n,M_n)\longrightarrow0,\qquad C=\bar C.$$
--
--   All logarithms are natural. The output-entropy bound applies only to the direct assertion and equality. This links the regularized information quantities to operational classical communication.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 8, Theorem 1: general quantum-channel coding theorem (seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 1, PDF pp.8-9. The converse has only finite C; the output entropy
bound is used only for the direct part and equality. No finite dimension or
separability restriction is imposed on I. -/
theorem generalChannelCoding {I : Type} [Nonempty I]
    (Phi : Matrix I I ℂ → Matrix I I ℂ) (hPhi : TC.IsTraceClassChannel Phi) :
    (informationCapacity Phi < ⊤ → ∀ R : ℝ,
      informationCapacity Phi < ENNReal.ofReal R →
      ¬ Tendsto (fun n : ℕ => quantumCodeError Phi n (natMessagesNats n R)) atTop (nhds 0)) ∧
    ((∃ B : ℝ≥0, ∀ rho : TC.State I,
        QE.extendedEntropyNats (Phi rho.coefficients) ≤ (B : ℝ≥0∞)) →
      (∀ R : ℝ, (R < 0 ∨ ENNReal.ofReal R < regularizedChannelHolevo Phi) →
        Tendsto (fun n : ℕ => quantumCodeError Phi n (natMessagesNats n R)) atTop (nhds 0)) ∧
      informationCapacity Phi = regularizedChannelHolevo Phi) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
