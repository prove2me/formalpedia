-- Prove2me | Theorems.Thm_StableMSR_Recovery_rational_recovery_program
-- name    : StableMSR.Recovery.rational_recovery_program
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-13T14:30:58.633893+00:00
-- url     : https://prove2.me/theorems/c2468a82-f9f1-431f-bb25-e0e414912c4f
-- title:
--   Deterministic recovery program at each fixed rational stability parameter
-- statement:
--   There are absolute positive integers $a,b$ such that, for every rational $\varepsilon\in(0,1)$, one can choose a finite admissible deterministic program $P$ before seeing any input instance. For every finite real metric $d$ on $n$ points and every $1\le k\le n$, the actual interpreter execution of $P$ halts within
--   $$a\,n^{bE(\varepsilon)}$$
--   steps and charged work, where $E$ is the exact Table 2 parameter envelope. Its output assigns each point a label in $\{0,\ldots,k-1\}$ and uses every label. If the instance has a $(1+\varepsilon)$-stable optimum under arbitrary symmetric perturbations, the decoded output equals that optimum.
--
--   The constants $a,b$ are independent of $\varepsilon,n,k,d$. The same halting and output guarantees hold on unstable inputs, and the $n=k=1$ case is included. The program receives only the canonical inputs $n,k,d$, with the two unused scalar slots fixed to zero; neither a stable optimum nor a certificate is input advice.
--
--   This is the remaining program-construction obligation for the recovery theorem, covering the deterministic search, local solver, order-family enumeration, and their implementation costs. The separate output-decoding lemma supplies feasibility from the validated labels; the separate parameter bound and rational calibration extend this statement to every real stability factor.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547v1, https://arxiv.org/html/2611.03547v1, Theorem 1.1; Section 4.4; Appendices A.4-A.6 and B; Appendix A.5 final paragraph (fixed rational parameter reduction).

import Definitions.Def_StableMSR_Recovery_Execution

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

/-- Uniform deterministic programs for rational stability parameters. The program
is selected before any input instance, and its charged interpreter execution
writes all k nonempty cluster labels. -/
theorem rational_recovery_program :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      ∀ ε₀ : ℚ, 0 < ε₀ → ε₀ < 1 →
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            ∃ t ≤ a * n ^ (b * parameterEnvelope (ε₀ : ℝ)),
              let s := execute P n k d t
              s.halted = true ∧
                s.work ≤ a * n ^ (b * parameterEnvelope (ε₀ : ℝ)) ∧
                ValidLabels n k s ∧
                ∀ O, Stable d k (1 + (ε₀ : ℝ)) O → outputPartition n k s = O := by sorry

end StableMSR.Recovery
