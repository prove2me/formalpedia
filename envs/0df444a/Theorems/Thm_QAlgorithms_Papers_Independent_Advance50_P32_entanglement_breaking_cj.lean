-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_entanglement_breaking_cj
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.entanglement_breaking_cj
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:18:19.505409+00:00
-- url     : https://prove2.me/theorems/000bf124-6548-44e1-b73f-15ccabd4a29e
-- title:
--   Theorem 4 (Choi-Jamiolkowski), with Appendix B proof
-- statement:
--   Let $\mathcal H$ be a nonzero separable complex Hilbert space. Write $\mathcal C_1(\mathcal H)$ for all complex trace-class operators and $\mathcal B(\mathcal H)$ for all bounded operators. Every entanglement-breaking channel $\Psi$ has a unique separable positive bounded operator $\Omega$ on $\mathcal H\otimes\mathcal H$, with the input factor first, such that
--
--   $$\operatorname{Tr}_{B}\Omega=I_A,\qquad \operatorname{Tr}[\Psi(A)B]=\langle\Omega,A\otimes B\rangle_{\mathrm{normal}}\quad(A\in\mathcal C_1(\mathcal H),\ B\in\mathcal B(\mathcal H)).$$
--
--   Conversely every such normalized separable bounded operator determines a unique entanglement-breaking channel on the full trace class. The pairing reconstructs a trace-class output for every $A$, and its finite-rank tests satisfy $\Omega_{(i,k),(j,l)}=\Psi(|j\rangle\langle i|)_{k,l}$. It is the normal trace-dual pairing specified by Appendix B, not the raw trace of a potentially non-trace-class tensor product. This states the correspondence without assuming $\Omega$ is trace class or restricting the channel to finitely many Kraus operators.
--
--   **Formalization Note** A nonempty countable orthonormal coordinate basis represents any such Hilbert space. The accepted separable-CJ predicate is transported from output-first to input-first order by the tensor flip. Channel uniqueness is equality on every trace-class input.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 11, Theorem 4, Eq. (24); Appendix B p.18

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology TensorProduct

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State IsTraceClassChannel BreaksTraceClassEntanglement
   productCoeff traceSize rotationMeasure)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P35 (tracePair)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel vacuum realFockTracePair)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Theorem 4, pp.10–11 and Appendix B, p.18: both directions, with uniqueness.
Any nonzero separable Hilbert space is represented by a nonempty countable basis.
Channel uniqueness is on EVERY trace-class input; arbitrary extensions outside
that domain are irrelevant. The normal pairing includes finite-rank agreement. -/
theorem entanglement_breaking_cj (I : Type) [Countable I] [Nonempty I] :
    (∀ T : FockOperatorArray I → FockOperatorArray I,
      IsTraceClassChannel T → BreaksTraceClassEntanglement T →
      ∃! O : FockOperatorArray (I × I), NormalizedSeparableCJ O ∧ CJCorresponds T O) ∧
    (∀ O : FockOperatorArray (I × I), NormalizedSeparableCJ O →
      ∃ T : FockOperatorArray I → FockOperatorArray I,
        IsTraceClassChannel T ∧ BreaksTraceClassEntanglement T ∧ CJCorresponds T O ∧
        ∀ S : FockOperatorArray I → FockOperatorArray I,
          IsTraceClassChannel S → BreaksTraceClassEntanglement S → CJCorresponds S O →
          ∀ A, IsTraceClass A → S A = T A) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
