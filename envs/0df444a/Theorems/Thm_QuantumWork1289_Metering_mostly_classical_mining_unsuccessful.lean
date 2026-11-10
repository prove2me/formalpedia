-- Prove2me | Theorems.Thm_QuantumWork1289_Metering_mostly_classical_mining_unsuccessful
-- name    : QuantumWork1289.Metering.mostly_classical_mining_unsuccessful
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T04:38:49.849905+00:00
-- url     : https://prove2.me/theorems/0e956f7e-b41c-491a-bbb1-ac697fcb4778
-- title:
--   Theorem 5 — Mostly classical mining is unsuccessful
-- statement:
--   Fix a positive security parameter $\lambda$, a fixed constant $a>0$, the setup nonce length, arbitrary valid fixed block strings $prev,tx$ independent of the oracles, and any allowed difficulty $0\le d\le d_{\max}(\lambda)$. Set $\Lambda_d=\lambda+2^d$, and let $\mathcal C_d\subseteq\Sigma_d^{N_d}$ be the family code at that parameter with list-recovery parameters $(\zeta,\ell,L)$. Write $N=N_d$ and $m=\lfloor\zeta N\rfloor$.
--
--   Let $A$ be any hybrid quantum miner whose initial state, advice and side resources are jointly independent of $H_{qz}$. It may choose the nonce and context adaptively and may use arbitrary private computation, persistent quantum memory and independent side-oracle access. Suppose every execution prefix makes at most $C$ measured classical queries and at most $Q$ coherent queries to $H_{qz}$, including preprocessing, with $C+1\le\ell$. The entire oracle $H_{qz}:\{0,1\}^*\to\{0,1\}^\lambda$ is sampled, and each query supplies its full answer. Then the actual Construction 2 acceptance probability obeys
--
--   $$\Pr_{\pi\leftarrow A(pp,prev,tx,d)}[\operatorname{Chk}(pp,prev,tx,d,\pi)=1]\le(C+1)L\,2^{-m}\sum_{j=0}^{\min\{Q,m\}}\binom mj.$$
--
--   The probability includes the sampled oracle and all miner randomness and measurements. Independent side randomness can be correlated with the initial advice; their joint specification is independent of the analyzed oracle. Malformed raw proofs and aborts reject. This result is stated for all list-recoverable finite-alphabet families with the same checker, and specializes to the source YZ family without changing its bound. No honest-solver correctness, rate, asymptotic condition or efficiency hypothesis is added.
--
--   Differences from the source:
--   - generalization: Construction 2 uses the specified Yamakawa–Zhandry folded Reed–Solomon family at Lambda_d = lambda + 2^d → the same Construction 2 checker for every finite-alphabet code family satisfying the source list-recovery property at that parameter; reason: the stated lower bound uses only list recovery; choosing the source YZ family and relabeling its finite alphabets by Fin recovers its full exact claim with the same N, zeta, ell and L
--   - encoding: random-oracle quantum algorithm with independent initial state and side resources → operational finite-register hybrid machine with arbitrary control, complete private instruments, independent seed/oracle product law, measurable Born probabilities and eventual halting success in ENNReal; reason: finite registers have an arbitrary dimension; the seed permits joint correlations among side resources and advice while enforcing joint independence from the analyzed oracle; finite horizons retain loops and preprocessing
--   - encoding: arbitrary mining proof strings, injective tuple encodings and first output bit of the lambda-bit XOR oracle → Option of raw bit lists, a fixed-width symbol parser, self-delimiting tuple framing, finite-alphabet labels and bit zero of a full Fin lambda to Bool answer; reason: abort, malformed length, trailing data and unused symbol encodings reject; coordinates map to i+1; every source proof and oracle address has an injective representation, with no restriction on any other oracle address or miner output
--   - encoding: allowed integer difficulty and real list-recovery parameters → natural difficulty bounded by the exact maxDifficulty, positive security, polynomial nonce-length function, real list bounds and ENNReal probability bounded by the exact real expression; reason: natural difficulties cover exactly the nonnegative allowed integers; positivity makes the first bit and logarithm defined; no rounding of L or ell and no additional lower bound on m or Q is imposed
-- source:
--   Mohammed Barhoush, Proof of Quantum Work with Classical Verification, STOC 2027 submission #1289 (October 2026), p. 24, Theorem 5, Eq. (13); exact simulation proof pp. 24–25; Construction 2 p. 23

import Definitions.Def_QuantumWork1289_Metering_construction
import Definitions.Def_QuantumWork1289_Metering_oracleExperiment
set_option autoImplicit false
open scoped ENNReal

namespace QuantumWork1289.Metering

/-- Barhoush, STOC 2027 submission #1289 (October 2026), p.24, Theorem 5, Eq.(13).
Generalized from the specified YZ family to every list-recoverable finite-alphabet family.
All security oracle output bits are supplied to A, including at malformed/out-of-scope addresses. -/
theorem mostly_classical_mining_unsuccessful
    {Ω S : Type} [MeasurableSpace Ω] {n C Q : ℕ}
    (p : Setup) (F : CodeFamily) (prev tx : Bits) (d : ℕ)
    (hd : d ≤ maxDifficulty p.security p.a) (ζ ℓ L : ℝ)
    (hcode : ListRecoverable (familyCode F (codeParameter p d)) ζ ℓ L)
    (hclassical : (C : ℝ) + 1 ≤ ℓ)
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A : SeededMachine Bits (OracleAnswer p.security) (Option Bits) Ω S n)
    (hbudget : ∀ ω, HasBudgets (A.machine ω) (A.initialState ω) C Q)
    (hmeasurable : MeasurableExecution A μ (checker p F prev tx d)) :
    successProbability A μ (checker p F prev tx d) ≤
      ENNReal.ofReal (((C : ℝ) + 1) * L *
        (2 : ℝ) ^ (-((unread ζ (F.length (codeParameter p d))) : ℤ)) *
        ∑ j ∈ Finset.range (min Q (unread ζ (F.length (codeParameter p d))) + 1),
          ((unread ζ (F.length (codeParameter p d))).choose j : ℝ)) := by sorry

end QuantumWork1289.Metering
