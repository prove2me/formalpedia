-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_pureLossCapacity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.pureLossCapacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:42:22.130987+00:00
-- url     : https://prove2.me/theorems/6372bf7e-fa94-42d2-9eb0-498d8efa42cb
-- title:
--   Eqs.(22)–(23): pure-loss quantum capacity, constrained and unconstrained
-- statement:
--   Let $0\le\eta\le1$ and $E\ge0$. Let $Q_E$ denote unassisted entanglement-transmission quantum capacity in qubits per mode, with mean photon number at most $E$ for the encoded maximally mixed logical state, and let $Q$ be its energy-unconstrained counterpart. For pure loss,
--
--   $$Q_E(\mathcal N[\eta,0])=\sup_{\rho:\,\langle\hat n\rangle_\rho\le E} I_c(\rho,\mathcal N[\eta,0])=\max\{g(\eta E)-g((1-\eta)E),0\}.$$
--
--   Here the supremum ranges over normalized finite-energy Fock states, $I_c$ is the output-minus-complement entropy in bits, and $g(x)=(1+x)\log_2(1+x)-x\log_2x$. Moreover,
--
--   $$Q(\mathcal N[\eta,0])=\begin{cases}\max\{\log_2(\eta/(1-\eta)),0\},&0<\eta<1,\\0,&\eta=0,\\+\infty,&\eta=1.\end{cases}$$
--
--   These formulas retain the zero-capacity antidegradable regime and the infinite identity-channel endpoint. The unconstrained value also equals the supremum, over finite nonnegative energy budgets, of the one-shot values above.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 5, Eqs.(22)–(23): pure-loss quantum capacity, constrained and unconstrained

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- PDF p.5 Eqs.(22)--(23), with provenance [16] Eq.(1), [13--15].
The unconstrained identity-channel endpoint is infinity, never log(1/0)=0.
On the antidegradable half the capacity is zero independently of printed Eq.(18). -/
theorem pureLossCapacity (eta budget : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (hbudget : 0 ≤ budget) :
    energyCapacity (coefficientChannel (C.thermal eta 0)) budget =
      ENNReal.ofReal (max (thermalEntropyBits (eta * budget) -
        thermalEntropyBits ((1 - eta) * budget)) 0) ∧
    oneShotPureLoss eta budget = ENNReal.ofReal (max (thermalEntropyBits (eta * budget) -
        thermalEntropyBits ((1 - eta) * budget)) 0) ∧
    T.operationalTraceClassCapacity (coefficientChannel (C.thermal eta 0)) =
      (⨆ energy : ℝ≥0, oneShotPureLoss eta (energy : ℝ)) ∧
    T.operationalTraceClassCapacity (coefficientChannel (C.thermal eta 0)) =
      if eta = 1 then ⊤ else ENNReal.ofReal (max (Real.logb 2 (eta / (1 - eta))) 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
