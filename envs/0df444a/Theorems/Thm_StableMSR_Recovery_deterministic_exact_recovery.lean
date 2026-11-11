-- Prove2me | Theorems.Thm_StableMSR_Recovery_deterministic_exact_recovery
-- name    : StableMSR.Recovery.deterministic_exact_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:20.848148+00:00
-- url     : https://prove2.me/theorems/6a8c0ab2-0fdc-46c1-beac-599a693f15ee
-- title:
--   Theorem 1.1 — deterministic exact recovery for every fixed stability factor
-- statement:
--   For every fixed real $\gamma>1$ there is a deterministic finite program, chosen before the input size, metric and cluster count. On every finite real metric input with $1\le k\le n$, it halts and returns exactly $k$ nonempty clusters. If the instance is $\gamma$-stable under all arbitrary symmetric perturbations, its output is the unique optimum.
--
--   There are absolute positive constants $a,b,C$, independent of $\gamma$ and all inputs. For $1<\gamma<2$, choose a fixed rational $\varepsilon_0$ with $(\gamma-1)/2\le\varepsilon_0<\gamma-1$; for $\gamma\ge2$, use $\varepsilon_0=1/2$. With $E(\varepsilon)=N_\varepsilon+F_\varepsilon+h_\varepsilon(\omega_\varepsilon+1)+1$ from Table 2,
--   $$
--   T\le a\,n^{b E(\varepsilon_0)},\qquad
--   E(\varepsilon_0)\le\frac{C}{(\gamma-1)^5}\quad(1<\gamma<2).
--   $$
--   Thus the source's inverse-fifth exponent is retained on arbitrary real metrics, and the runtime also bounds unstable inputs. The $n=k=1$ case is included through the absolute prefactor. Every step is charged by the interpreter; neither a stable optimum nor a certificate is input advice.
--
--   This is the full primary recovery target. Section 3 and Appendix A.5 additionally state a polynomial rational-input bit overhead for this construction; that bit-cost refinement has not been formalized in the partial draft. The source algorithm and twelve supporting numbered items are also still missing, as recorded in HARD.md. This item is not a completed mission proposal.
--
--   Differences from the source:
--   - encoding: An arbitrary finite real metric space with fixed input order and unordered clusters → Points are Fin n; clusters and unordered partitions are finite sets; metric arrays are Mathlib metric distances; reason: Relabelling preserves every finite ordered instance, all distance values, and every unordered partition
--   - encoding: A deterministic algorithm in the exact-arithmetic/comparison model with n^{O((gamma-1)^-5)} runtime → An admissible finite deterministic instruction program and a halting execution within a times n^{b times the Table 2 parameter envelope}; reason: Actual interpreter execution supplies runtime; absolute a,b,C are chosen before gamma and all input data. The envelope is bounded by C/(gamma-1)^5
--   - encoding: Appendix A.5 chooses a fixed rational gamma0 with (gamma-1)/2 <= gamma0-1 < gamma-1, and uses 3/2 for gamma >= 2 → An existential rational epsilon0 in that interval, equal to 1/2 for gamma >= 2, is chosen before the finite program and all inputs; reason: No real metric or real stability factor is excluded; rational constants are hardcoded into the chosen program. The two unused machine scalar slots are fixed to zero
--   - encoding: An unordered feasible exact-k partition → Validated surjective labels decoded to an unordered finite set of nonempty fibers; reason: Labels supply a concrete output representation; equality and uniqueness are tested on the unordered decoded partition
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Theorem 1.1, p. 2; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Execution

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

/-- Theorem 1.1: finite programs precede all input data; every runtime is interpreter execution.
The parameter-envelope witness records the explicit bound of Appendix A.5. -/
theorem deterministic_exact_recovery :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        ((γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5)) ∧
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            RecoversWithin P n k d γ (a * n ^ (b * parameterEnvelope (ε₀ : ℝ))) := by sorry

end StableMSR.Recovery
