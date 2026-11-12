-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P33_ratePolynomialOptimum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P33.ratePolynomialOptimum
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T06:51:49.304404+00:00
-- url     : https://prove2.me/theorems/aa4364fc-4615-4c0a-8166-8099fb542d77
-- title:
--   III.C.1: exact optimization of the displayed rate polynomial, (16)–(18)
-- statement:
--   Let $0<t<1$, $0<t_B\le1$, $0<\eta\le1$, and $0\le f<1$. Regard the expression displayed in (16) solely as the polynomial
--
--   $$
--   P(\mu)=\mu t t_B\eta(1-f)\bigl[1-\mu(1-t)\bigr],\qquad \mu\ge0.
--   $$
--
--   Its unique maximizer and maximum are
--
--   $$
--   \mu_*={1\over2(1-t)},\qquad P(\mu_*)={t t_B\eta(1-f)\over4(1-t)}.
--   $$
--
--   For every $\mu\ge0$, $P(\mu)\le P(\mu_*)$, with equality exactly when $\mu=\mu_*$. The strictly lossy domain avoids division by zero and the positive prefactors exclude the identically zero polynomial.
--
--   This is the page's exact algebraic optimization. It does not identify the polynomial with an operational secure-key rate or certify an approximation regime.
-- source:
--   Towards practical and fast Quantum Cryptography, arXiv:quant-ph/0411022v1, PDF p. 5, III.C.1, (16)–(18)

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

/-- PDF p.5, (16)-(18): exact optimization of the printed polynomial over mu≥0.
Strictly lossy t and positive prefactors are the nontrivial protocol branch.
This is not a secure-key achievability or security theorem. -/
theorem ratePolynomialOptimum (t tB eta f : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (htB : 0 < tB) (htB1 : tB ≤ 1)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hf : 0 ≤ f) (hf1 : f < 1) :
    let muOpt := 1 / (2 * (1 - t))
    0 < muOpt ∧
    ratePolynomial t tB eta f muOpt = t * tB * eta * (1 - f) / (4 * (1 - t)) ∧
    (∀ mu : ℝ, 0 ≤ mu →
      ratePolynomial t tB eta f mu ≤ ratePolynomial t tB eta f muOpt) ∧
    (∀ mu : ℝ, 0 ≤ mu →
      (ratePolynomial t tB eta f mu = ratePolynomial t tB eta f muOpt ↔ mu = muOpt)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P33

end
