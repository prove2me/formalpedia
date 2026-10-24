-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_independentPauli_privateCapacity_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P07.independentPauli_privateCapacity_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:57:15.152373+00:00
-- url     : https://prove2.me/theorems/9b91d071-ca66-43eb-915e-c4b9e4253ba0
-- title:
--   Section IV.B: amplitude-damping bound for independent phase/amplitude errors
-- statement:
--   Let $0\le q\le1/2$ and define $\mathcal N_q(\rho)=(1-q(2-q))\rho+q(1-q)X\rho X+q^2Y\rho Y+q(1-q)Z\rho Z$. Set $\gamma_q=4q(1-q)$ and $f(\gamma)=\max_{t\in[0,1]}[H(t(1-\gamma))-H(t\gamma)]$. Then
--
--   $$C_p(\mathcal N_q)\le f(\gamma_q).$$
--
--   All quantum registers are finite and nonzero, states have trace one, pure vectors have norm one, and entropy and logarithms are in bits. Operational private capacities use memoryless powers, positive blocklengths and message counts, uniform messages, arbitrary mixed block inputs, and normalized decoding POVMs. A code is good when its joint decoded message/environment state has full trace norm less than the error from a perfectly correlated uniform pair tensor its actual common environment marginal. Rates use every positive error and rate slack at all sufficiently large blocklengths. Symmetric assistance allows one arbitrary finite symmetric channel per block without charging its dimension.
--
--   This result supplies a capacity identity or bound for the channel family and resource model stated above.
--
--   The exact decomposition is retained: with $R=(I+iX)/\sqrt2$ and $\gamma=4q(1-q)$,
--
--   $$\mathcal N_q(\rho)=\tfrac12R\operatorname{AD}_\gamma(R^\dagger\rho R)R^\dagger+\tfrac12RX\operatorname{AD}_\gamma(XR^\dagger\rho RX)XR^\dagger.$$
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 6, Section IV.B: amplitude-damping bound for independent phase/amplitude errors

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Support50.P07

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
    dilationPower idealJoint maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

variable {A B E C D F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

variable [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]

/-- Section IV.B, PDF p.6, SOURCE DOMAIN CORRECTION: the printed rotated damping
identity uses sqrt((1-2q)^2)=1-2q, so only its q<=1/2 branch is transcribed. At q=1
it would identify conjugation by Y with the identity. The exact equal mixture is
retained, with R=(I+iX)/sqrt(2)=exp(i*pi*X/4). No all-q relabeling is assumed. -/
theorem independentPauli_privateCapacity_bound [Nonempty E]
    (U : Matrix (Fin 2 × E) (Fin 2) ℂ)
    (hU : IsIsometry U) (q : ℝ) (hq : q ∈ Set.Icc 0 (1 / 2))
    (hmap : receiverChannel U = independentPauliChannel q) :
    let rot : Matrix (Fin 2) (Fin 2) ℂ :=
      (Real.sqrt 2 : ℂ)⁻¹ • (1 + Complex.I • pauliMatrices 1)
    independentPauliChannel q = (fun rho =>
      (1 / 2 : ℂ) •
        (rot * amplitudeDampingChannel (4 * q * (1 - q)) (rotᴴ * rho * rot) * rotᴴ) +
      (1 / 2 : ℂ) •
        (rot * pauliMatrices 1 *
          amplitudeDampingChannel (4 * q * (1 - q))
            (pauliMatrices 1 * rotᴴ * rho * rot * pauliMatrices 1) *
          pauliMatrices 1 * rotᴴ)) ∧
    fullTracePrivateCapacity U ≤ dampingBound (4 * q * (1 - q)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
