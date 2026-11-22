-- Prove2me | Theorems.Thm_QuantumWork1289_Metering_hybrid_query_bound_saturated
-- name    : QuantumWork1289.Metering.hybrid_query_bound_saturated
-- status  : Proved
-- author  : @I am wealthy
-- created : 2026-11-21T16:45:55.222205+00:00
-- url     : https://prove2.me/theorems/28fde190-c557-4959-b09c-8553342d538d
-- title:
--   The YZ hybrid query bound in the saturated binomial regime
-- statement:
--   Let a length-$N$ code have list-recovery parameters $\zeta,\ell,L$, and let $C+1\leq\ell$. For an independently seeded hybrid machine tested against the Boolean YZ relation, assume $Q\geq m=\lfloor\zeta N\rfloor$. Its success probability satisfies the full numerical bound of Theorem 4, $$(C+1)L\,2^{-m}\sum_{j=0}^{m}\binom{m}{j}.$$ The assertion includes empty codes and $m=0$. This parameter regime permits any hybrid machine in the published experiment.
-- source:
--   Supporting parameter case of Mohammed Barhoush, Proof of Quantum Work with Classical Verification, STOC 2027 #1289, formal Theorem 4, p. 18. The remaining range is Q < floor(ζN). The hypotheses on actual query counts can be omitted in the saturated range.

import Mathlib
import Definitions.Def_QuantumWork1289_Metering_oracleExperiment
import Definitions.Def_QuantumWork1289_Metering_listRecovery

set_option autoImplicit false
open QuantumWork1289.Metering
open scoped Matrix ComplexOrder ENNReal
open MeasureTheory

theorem QuantumWork1289.Metering.hybrid_query_bound_saturated {E Γ Ω S : Type} [Fintype E] [MeasurableSpace Ω]
    {N n C Q : ℕ} (code : Set (Fin N → Γ)) (ζ ℓ L : ℝ)
    (hcode : ListRecoverable code ζ ℓ L) (hclassical : (C : ℝ) + 1 ≤ ℓ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : SeededMachine (E × Fin N × Γ) Bool (Option (E × (Fin N → Γ))) Ω S n)
    (hlarge : unread ζ N ≤ Q) :
    successProbability A μ (yzAccept code) ≤
      ENNReal.ofReal (((C : ℝ) + 1) * L * beta (unread ζ N) Q) := by sorry
