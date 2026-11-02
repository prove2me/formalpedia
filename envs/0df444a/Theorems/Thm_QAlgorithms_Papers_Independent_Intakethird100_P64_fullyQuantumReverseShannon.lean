-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P64_fullyQuantumReverseShannon
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P64.fullyQuantumReverseShannon
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:33:36.533284+00:00
-- url     : https://prove2.me/theorems/1f9c855a-d6cc-41ae-8e39-750b6f8acd25
-- title:
--   Fully quantum reverse Shannon with feedback and a relative input promise
-- statement:
--   Let $R,S,A,B$ be finite nonzero complex registers. Alice controls $S$ and retains $A$; Bob receives $B$. Let $U:S\to A\otimes B$ be an isometry, let $\rho$ be a density matrix on $S$, and let $|\phi\rangle^{RS}$ be a unit purification of $\rho$. Set $|\psi\rangle=(I_R\otimes U)|\phi\rangle$. Entropies are in bits and $I(X;Y)=H(X)+H(Y)-H(XY)$.
--
--   Then the following asymptotic resource inequality holds:
--
--   $$
--   \tfrac12 I(R;B)_\psi[q\to q]+\tfrac12 I(A;B)_\psi[qq]\ge\langle U:\rho\rangle.
--   $$
--
--   For every error $\varepsilon>0$ and rate slack $\delta>0$, there are $\eta>0$ and a threshold $N$ such that every $n\ge N$, $n\ge1$ admits local physical encoding and decoding operations. They consume at most $\lfloor n(I(R;B)_\psi/2+\delta)\rfloor$ forward qubits and $\lfloor n(I(A;B)_\psi/2+\delta)\rfloor$ normalized Bell pairs. These operations are chosen before any test input. For every finite reference $T$ and joint density $\sigma^{TS^n}$ whose $S^n$ marginal is within full trace norm $\eta$ of $\rho^{\otimes n}$, the complete output on $T,A^n,B^n$ is within full trace norm $\varepsilon$ of $(I_T\otimes U^{\otimes n})\sigma(I_T\otimes U^{\otimes n})^\dagger$. No nonlocal assistance is left uncounted.
--
--   This is the simulation arm of reversible feedback-channel decomposition; the source attributes its coherent construction to [9].
-- source:
--   A triangle of dualities: reversibly decomposable quantum channels, source-channel duality, and time reversal, arXiv:quant-ph/0505138v1, PDF p. 2, Equation (5): fully quantum reverse Shannon inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P64

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P64

open QAlgorithms

open QAlgorithms.Papers.Independent.Gap48.P20
  (Copies redistributionMarginal subsystemEntropy forwardApply)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, (5), attributed there to [9]: fully quantum reverse Shannon.
U is a feedback isometry, rho is a density matrix, phi its normalized purification,
and the two coefficients are computed from (id_R tensor U)phi. Simulation includes
Alice's feedback and every allowed reference correlation, under the near-IID promise. -/
theorem fullyQuantumReverseShannon {R S A B : Type}
    [Fintype R] [Fintype S] [Fintype A] [Fintype B]
    [Nonempty R] [Nonempty S] [Nonempty A] [Nonempty B]
    (U : Matrix (A × B) S ℂ) (hU : Uᴴ * U = 1)
    (rho : Matrix S S ℂ) (hrho : IsDensityMatrix rho)
    (phi : EuclideanSpace ℂ (R × S)) (hphi : IsState phi)
    (hpurification : traceLeft (pureDensity phi) = rho) :
    RelativeSimulationAchievable U rho
      (mutualRB (feedbackOutputVector U phi) / 2) (mutualAB (feedbackOutputVector U phi) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P64

end
