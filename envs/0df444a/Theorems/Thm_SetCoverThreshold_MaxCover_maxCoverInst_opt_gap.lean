-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_maxCoverInst_opt_gap
-- name    : SetCoverThreshold.MaxCover.maxCoverInst_opt_gap
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T19:42:40.695952+00:00
-- url     : https://prove2.me/theorems/4ea3a185-98d9-44da-8c24-4dafb6ca1f59
-- title:
--   Optimum Gap of the Section 5 Max k-Cover Instance (Theorem 5.3)
-- statement:
--   This theorem establishes the optimum approximation gap for the Max $k$-Cover reduction instance $\text{maxCoverInst}(\phi, C)$ (Feige 1998, Section 5, p. 649, proof of Theorem 5.3), assuming Raz's Parallel Repetition Theorem.
--
--   The theorem asserts two complementary properties:
--
--   1. **Completeness (Yes instance):** If the 3CNF-5 formula $\phi$ is satisfiable, then for any $k, \ell \ge 1$ and code $C : [k] \to \{0,1\}^\ell$, the optimal cover achieves full coverage:
--   $$
--   \text{opt}(\text{maxCoverInst}(\phi, C)) = N,
--   $$
--   where $N = (\text{maxCoverInst}(\phi, C)).n$ is the total number of points in the ground set.
--
--   2. **Soundness (No instance):** For every $\varepsilon > 0$, there exists an integer $k_0$ such that for all $k \ge k_0$ and every $\varepsilon' > 0$, there exists $\ell_0$ such that for all $\ell \ge \ell_0$, for any valid code $C$, if at most a $(1 - \varepsilon')$-fraction of clauses in $\phi$ are simultaneously satisfiable, then:
--   $$
--   \text{opt}(\text{maxCoverInst}(\phi, C)) \le \left(1 - \frac{1}{e} + \varepsilon\right) N.
--   $$
--
--   This gap establishes that distinguishing between fully coverable instances and instances with cover fraction at most $1 - 1/e + \varepsilon$ is as hard as distinguishing satisfiable formulas from unsatisfiable ones.
-- source:
--   Uriel Feige, A Threshold of ln n for Approximating Set Cover, Journal of the ACM 45(4):634-652 (1998), p. 649, proof of Theorem 5.3

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Instance
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction
import Definitions.Def_SetCoverThreshold_MaxCover_Theorem53

open CookPvsNP

namespace SetCoverThreshold.MaxCover

theorem maxCoverInst_opt_gap (hRaz : RazRepetition) :
    (∀ (k ℓ : ℕ) (code : Fin k → Fin ℓ → Bool) (φ : Formula5), φ.toCNF.Satisfiable →
        opt (maxCoverInst φ code) = (maxCoverInst φ code).n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
        ∀ code : Fin k → Fin ℓ → Bool, IsCode code →
          ∀ φ : Formula5, AtMostFracSat (1 - ε') φ.toCNF →
            (opt (maxCoverInst φ code) : ℝ) ≤
              (1 - Real.exp (-1) + ε) * ((maxCoverInst φ code).n : ℝ)) := by sorry

end SetCoverThreshold.MaxCover
