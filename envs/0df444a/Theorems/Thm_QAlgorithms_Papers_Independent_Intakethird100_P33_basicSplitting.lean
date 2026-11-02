-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P33_basicSplitting
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P33.basicSplitting
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:50:52.111043+00:00
-- url     : https://prove2.me/theorems/588c16bb-af46-4ebe-bafb-bbcb011cace0
-- title:
--   III.C.1: basic splitting preserves Bob and reveals the bit on an Eve click, (15)
-- statement:
--   Let $\mu\ge0$ and $t\in[0,1]$. A nondecoy source bit $b\in\{0,1\}$ is the normalized coherent product $|\psi_b(\mu)\rangle$, occupied in its early bin for $b=0$ and late bin for $b=1$. Apply the vacuum beam splitter of intensity transmission $t$ separately to both bins, using its full normalized number-basis coefficients and positive output phases. The normalized output and Bob marginal are
--
--   $$
--   |\Psi_b\rangle=|\psi_b(\mu t)\rangle_B\otimes|\psi_b(\mu(1-t))\rangle_E,
--   \qquad \rho_B^b=|\psi_b(\mu t)\rangle\langle\psi_b(\mu t)|.
--   $$
--
--   Thus Bob's state is the state of the untouched lossy channel. An ideal time-bin click on Eve's part reveals the bit without error. Its probability is $p_E=1-e^{-\mu(1-t)}$, independently of $b$. If $\mu(1-t)>0$, let $K(p,y)$ be any finite-output trusted stochastic readout of Bob's two photon occupations $p$: $K\ge0$ and $\sum_y K(p,y)=1$. This kernel does not depend on Eve's outcome. With equal nondecoy bit priors, the normalized joint law of Bob's output $Y$ and Eve's inferred bit $E$, conditional on her click, equals the original joint law of $Y$ and Alice's bit $A$. In particular,
--
--   $$
--   I(Y:E\mid D_E)=I(Y:A).
--   $$
--
--   Equality of the joint laws also permits the same subsequent Bob acceptance conditioning and throughput weighting. At zero Eve-click probability, only the optical product and marginal statements apply. The exponential click probability is not replaced by its mean $\mu(1-t)$.
--
--   This pins the exact content of the specified basic splitting attack and (15), without an optimality, privacy-amplification, or exact first-order Bob-rate assertion.
-- source:
--   Towards practical and fast Quantum Cryptography, arXiv:quant-ph/0411022v1, PDF p. 5, III.C.1, Fig.2 and (15)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P33

open scoped BigOperators ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity rankOne)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P48 (vacuumAmplitude)

open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM realFockTracePair)

open QAlgorithms.Papers.Independent.Dependency50.P34
  (TwoModeFock fockKet photonMean)

open QAlgorithms.Papers.Independent.Frontier18.P14
  (coherentPair coherentPairCoefficients)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.4-5, Fig.2 and (15): the full vacuum beam splitter produces a product
of attenuated coherent trains. Bob's marginal equals the untouched lossy channel.
On Eve's positive-probability click event the exact joint law equals Alice-Bob's
law, for arbitrary finite trusted number-readout/noise K. The probability used
here is exponential; the source's mu*(1-t) leakage claim is deferred separately.
Equality of joint laws also preserves subsequent Bob acceptance conditioning and
its common throughput weight; no first-order detection rate is asserted. -/
theorem basicSplitting (mu t : ℝ) (hmu : 0 ≤ mu) (ht : t ∈ Set.Icc 0 1) :
    (∀ bit : Bool,
      Memℓp (splitCoefficients t (dataState mu bit)) 2 ∧
      ‖dataState mu bit‖ = 1 ∧ ‖dataState (mu * t) bit‖ = 1 ∧
      ‖dataState (mu * (1 - t)) bit‖ = 1 ∧
      ‖splitState t (dataState mu bit)‖ = 1 ∧
      (∀ p q, splitState t (dataState mu bit) (p, q) =
        dataState (mu * t) bit p * dataState (mu * (1 - t)) bit q) ∧
      (∀ p q, Summable (fun e : ℕ × ℕ =>
        splitState t (dataState mu bit) (p, e) * star (splitState t (dataState mu bit) (q, e)))) ∧
      splitBobDensity t (dataState mu bit) = rankOne (dataState (mu * t) bit)) ∧
    (∀ bit : Bool, ∀ q, eveReadout q = some (!bit) →
      dataState (mu * (1 - t)) bit q = 0) ∧
    eveClickProbability mu t = 1 - Real.exp (-mu * (1 - t)) ∧
    (0 < mu * (1 - t) →
      0 < eveClickProbability mu t ∧
      ∀ (O : Type) [Fintype O] (K : (ℕ × ℕ) → O → ℝ),
        (∀ p o, 0 ≤ K p o) → (∀ p, ∑ o, K p o = 1) →
        clickJoint K mu t = aliceBobJoint K mu t ∧
        (∀ o b, 0 ≤ clickJoint K mu t o b) ∧
        (∑ o, ∑ b : Bool, clickJoint K mu t o b) = 1 ∧
        QAlgorithms.mutualInfoBits (Function.uncurry (clickJoint K mu t)) =
          QAlgorithms.mutualInfoBits (Function.uncurry (aliceBobJoint K mu t))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P33

end
