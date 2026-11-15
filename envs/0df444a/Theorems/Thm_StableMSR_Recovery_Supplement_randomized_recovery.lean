-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_randomized_recovery
-- name    : StableMSR.Recovery.Supplement.randomized_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:15:11.871773+00:00
-- url     : https://prove2.me/theorems/aff88e2e-2c0b-4177-bd97-8cc2c59f7a4f
-- title:
--   Theorem 4.5 — randomized exact recovery
-- statement:
--   For every fixed real $1<\gamma<2$, put $\varepsilon=\gamma-1$. There is an admissible finite program, selected before the input, that always halts and returns a feasible exact-$k$ partition on every finite real metric input with $1\le k\le n$. For every $\gamma$-stable optimum $\mathcal O$,
--
--   $$\Pr[\text{output}\ne\mathcal O]\le\frac23,\qquad
--   \Pr[\text{a cheapest output of }m\text{ independent runs}\ne\mathcal O]\le(2/3)^m\quad(m\ge1).$$
--
--   The halting and feasibility guarantees hold for every tape, including on unstable inputs and for $k=n$. There are absolute positive $a,b,C$, independent of $\gamma$ and every instance. Choose a fixed rational $\varepsilon_0$ with $\varepsilon/2\le\varepsilon_0<\varepsilon$. If $E(u)=N_u+F_u+h_u(\omega_u+1)+1$ is the published Table 2 envelope, both steps and charged work are bounded by
--
--   $$a n^{bE(\varepsilon_0)},\qquad E(\varepsilon_0)\le C/\varepsilon^5.$$
--
--   This retains the exact inverse-fifth exponent. The repeated-run assertion covers every cheapest-output tie-breaking rule. It supplies the randomized precursor to the goal; the theorem does not require its witness program to consume randomness.
--
--   Differences from the source:
--   - encoding: Finite ordered metric input and unordered exact-k partitions → Fin n points, real metric arrays, and finite sets of nonempty disjoint blocks; reason: Input-order relabelling preserves every source instance and partition; base published definitions are reused without extra conditions
--   - reading: Algorithm 1 randomized recovery guarantee → Existence of an admissible finite program with those guarantees, without prescribing its instruction list; reason: As directed by the supplement brief, this is the same algorithm-existence reading as the published goal; randomness is allowed and is not required to be used
--   - encoding: n^O(epsilon^-5) in the exact arithmetic/comparison model → Actual interpreter steps and charged work at most a*n^(b*parameterEnvelope epsilon0), with absolute a,b,C and rational calibration before all input data; reason: Appendix A.5 gives the Table 2 exponent envelope and epsilon/2 <= epsilon0 < epsilon; neither real metrics nor real gamma are restricted
--   - encoding: Success probability at least 1/3 and independent-run amplification → Outer-measure failure upper bounds under tapeLaw and its m-fold product; every minimizing output is covered; reason: Failure bounds retain the numerical probabilities and do not obtain a lower bound from a potentially nonmeasurable event
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Theorem 4.5, p. 11; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Supplement_RandomExecution

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

/-- Finite programs are chosen before the input. The existential program reading is shared
with the published goal; it does not require the program to draw a random value. -/
theorem randomized_recovery :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → γ < 2 → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1 ∧
        (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5 ∧
        ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            let budget := a * n ^ (b * parameterEnvelope (ε₀ : ℝ))
            AlwaysFeasible P n k d budget ∧
            ∀ O, Stable d k γ O →
              MinSumFPT.tapeLaw {ω | randomOutput P n k d budget ω ≠ O} ≤ (2 / 3 : ENNReal) ∧
              ∀ m : ℕ, 1 ≤ m →
                independentTapes m {ω | CheapestFailure P n k d budget m O ω} ≤
                  (2 / 3 : ENNReal) ^ m := by sorry

end StableMSR.Recovery.Supplement
