-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_ideal_singlet_key
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.ideal_singlet_key
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:16:37.198779+00:00
-- url     : https://prove2.me/theorems/f03e5d95-f3f1-4450-a737-9e08c469b93b
-- title:
--   Exact singlets yield a uniform secret shared key
-- statement:
--   Let $R\ge0$ and let $\rho_{ABE}$ be any normalized joint state whose $AB$ marginal is the product of $R$ singlets. The finite reference $E$ has arbitrary dimension. Alice and Bob measure each corresponding qubit along the same arbitrary axis. For any strings $a,b\in\{0,1\}^R$ and any measurable event $S$ of any measurement on Eve's reference,
--
--   $$\Pr[A=a,B=b,E\in S]=2^{-R}\mathbf1_{b=\overline a}\Pr[E\in S].$$
--
--   Consequently Alice's key is uniform, Bob obtains the same key by complementing his outcomes, and Eve's outcomes are independent of the key. The formula includes the empty key.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 4, Exact singlets yield a uniform secret shared key

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF p.4: exact singlets give a uniform shared key after Bob complements his bits,
independent of every measurement on an arbitrary finite reference. The empty key is included. -/
theorem ideal_singlet_key {E Y : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace Y] (R : ℕ)
    (rho : Matrix (PairRegister R × E) (PairRegister R × E) ℂ)
    (hrho : IsDensityMatrix rho) (hAB : traceRight rho = pureDensity (singletKet R))
    (U : Matrix.unitaryGroup Bool ℂ) (Q : OperatorPOVM E Y)
    (a b : Qubits R) (S : Set Y) (hS : MeasurableSet S) :
    idealKeyLaw rho U Q a b S =
      if b = (fun i => !(a i)) then
        (2 : ℝ)⁻¹ ^ R * effectProb (Q.operator S) (traceLeft rho) else 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
