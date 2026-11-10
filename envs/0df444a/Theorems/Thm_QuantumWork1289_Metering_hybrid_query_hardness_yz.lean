-- Prove2me | Theorems.Thm_QuantumWork1289_Metering_hybrid_query_hardness_yz
-- name    : QuantumWork1289.Metering.hybrid_query_hardness_yz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:38:54.456132+00:00
-- url     : https://prove2.me/theorems/f1817e14-c2a9-43c4-b6b1-f92b49809846
-- title:
--   Theorem 4 — Hybrid-query hardness of YZ
-- statement:
--   Let $\mathcal C\subseteq\Sigma^N$ be $(\zeta,\ell,L)$-list recoverable, with $0<\zeta<1$, and let $\mathcal E$ be a finite context set. The alphabet and code need not be finite. Sample a uniform Boolean oracle $F:\mathcal E\times[N]\times\Sigma\to\{0,1\}$.
--
--   Let $A$ be any hybrid quantum algorithm with free side resources jointly independent of $F$ together with its initial state. It may interleave arbitrary private computation, measurements, at most $C$ measured classical reads and at most $Q$ coherent oracle calls, with $C+1\le\ell$. All preprocessing calls count, and quantum memory persists across classical calls. Its probability of outputting $(\eta,w)$ with $w\in\mathcal C$ and $F(\eta,i,w_i)=0$ at every coordinate is at most
--
--   $$\Pr[A\text{ solves the YZ relation}]\le(C+1)L\,2^{-m}\sum_{j=0}^{\min\{Q,m\}}\binom mj,\qquad m=\lfloor\zeta N\rfloor.$$
--
--   This is the exact arbitrary-context bound needed for the mining theorem. It includes $C=Q=0$, $m=0$, and $Q\ge m$. No conditional uniformity after observing a quantum transcript is assumed. The probability is computed from the operational experiment, and a bona fide stochastic execution is required to be measurable.
--
--   Differences from the source:
--   - encoding: random-oracle quantum algorithm with independent initial state and side resources → operational finite-register hybrid machine with arbitrary control, complete private instruments, independent seed/oracle product law, measurable Born probabilities and eventual halting success in ENNReal; reason: finite registers have an arbitrary dimension; the seed permits joint correlations among side resources and advice while enforcing joint independence from the analyzed oracle; finite horizons retain loops and preprocessing
--   - encoding: one-based coordinates, real cardinality bounds and the exact floor/binomial expression → Fin N with one-based external encoding, finite-subset cardinality bounds, natural floor and a real integer power with an inclusive range sum; reason: these encodings preserve all instances, constants and boundary cases without assuming finite alphabets for Theorem 4
-- source:
--   Mohammed Barhoush, Proof of Quantum Work with Classical Verification, STOC 2027 submission #1289 (October 2026), p. 18, formal Theorem 4; proof pp. 18–22, Eqs. (2)–(8)

import Definitions.Def_QuantumWork1289_Metering_listRecovery
import Definitions.Def_QuantumWork1289_Metering_oracleExperiment
set_option autoImplicit false
open scoped ENNReal

namespace QuantumWork1289.Metering

/-- Barhoush, STOC 2027 submission #1289 (October 2026), p.18, formal Theorem 4.
The probability is computed by operational hybrid executions against a full product oracle. -/
theorem hybrid_query_hardness_yz
    {E Γ Ω S : Type} [Fintype E] [MeasurableSpace Ω]
    {N n C Q : ℕ} (code : Set (Fin N → Γ)) (ζ ℓ L : ℝ)
    (hcode : ListRecoverable code ζ ℓ L) (hclassical : (C : ℝ) + 1 ≤ ℓ)
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A : SeededMachine (E × Fin N × Γ) Bool (Option (E × (Fin N → Γ))) Ω S n)
    (hbudget : ∀ ω, HasBudgets (A.machine ω) (A.initialState ω) C Q)
    (hmeasurable : MeasurableExecution A μ (yzAccept code)) :
    successProbability A μ (yzAccept code) ≤
      ENNReal.ofReal (((C : ℝ) + 1) * L * beta (unread ζ N) Q) := by sorry

end QuantumWork1289.Metering
