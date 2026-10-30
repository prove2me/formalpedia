-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P34_controlledPhase_feedforward_composes
-- name    : QAlgorithms.Papers.Independent.Advance50.P34.controlledPhase_feedforward_composes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:37:34.917777+00:00
-- url     : https://prove2.me/theorems/014646d1-6667-4321-9240-3b79c0ef8241
-- title:
--   Controlled-phase feedforward propagation preserves the output channel
-- statement:
--   Use the full two-oscillator Hilbert space, with optical quadratures $[x_j,p_k]=i\delta_{jk}/2$ and vacuum variance $1/4$. Put $R=(x_1,p_1,x_2,p_2)^T$, and let $M$ send $(a,b,c,d)$ to $(a,b+c,c,d+a)$. There exists a bounded controlled-phase unitary $U$, characterized up to scalar phase by $U^*e^{i k^T R}U=e^{i (M^T k)^T R}$ for every real $k$; it represents $C_Z=e^{2i x_1x_2}$.
--
--   For every real displacement vector $s=(a,b,c,d)$ there are actual Weyl displacement unitaries $D(s)$ and $D(Ms)$, fixed independently of the input. Let $\mathcal U(\rho)=U\rho U^*$ and $\mathcal D_s(\rho)=D(s)\rho D(s)^*$. For every normalized density operator $\rho$ on the two modes and any countable-basis spectator system $A$, including arbitrary correlations with $A$,
--
--   $$
--   (\mathcal U\otimes\operatorname{id}_A)\bigl((\mathcal D_s\otimes\operatorname{id}_A)(\rho)\bigr)
--   =(\mathcal D_{Ms}\otimes\operatorname{id}_A)\bigl((\mathcal U\otimes\operatorname{id}_A)(\rho)\bigr).
--   $$
--
--   This is the ideal displacement propagation rule used to incorporate the gate into a larger cluster computation while retaining its wire continuations. It makes no assertion that finite-squeezing noise is removed.
--
--   **Formalization Note** Densities are positive nuclear trace-class operators of trace one on the completed Fock space. Symmetric Weyl displacements and the source's ordered position/momentum displacements differ only by scalar phase, which cancels at the channel level.
-- source:
--   Demonstration of a Controlled-Phase Gate for Continuous-Variable One-Way Quantum Computation, arXiv:1107.0514v1, PDF p. 2, Fig.1(b) and authors’ note [18], PDF p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P34

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Advance50.P34

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff boundedUnitaryConjugation)

/-- PDF p.2, Fig.1(b), and PDF p.4, authors' note [18]: displacement feedforward
can be moved through the ideal C_Z by the classical update s -> M s, preserving
the output density, including correlations with arbitrary spectator modes.
The same gate and the same displacement realizations work for every input.
This is the ideal gate propagation rule used when retaining the wire continuations;
it neither discards finite-squeezing noise nor postulates an infinite-squeezing state. -/
theorem controlledPhase_feedforward_composes :
    ∃ U : Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ),
      RealizesControlledPhase U ∧
      ∀ s : Fin 4 → ℝ,
        ∃ V Vout : Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ),
          unitaryCoeff V = twoModeDisplacement s ∧
          unitaryCoeff Vout = twoModeDisplacement (controlledPhaseShear s) ∧
          ∀ (A : Type) [Countable A] (rho : State ((ℕ × ℕ) × A)),
            tensorApply (boundedUnitaryConjugation U)
              (tensorApply (boundedUnitaryConjugation V) rho.coefficients) =
            tensorApply (boundedUnitaryConjugation Vout)
              (tensorApply (boundedUnitaryConjugation U) rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P34

end
