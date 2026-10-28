-- Prove2me | Theorems.Thm_ShadowTomography_ClassicalLB_entropy_bound
-- name    : ShadowTomography.ClassicalLB.entropy_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:28:54.258282+00:00
-- url     : https://prove2.me/theorems/bbdac246-d2a5-4cbd-86c2-506dca217cfb
-- title:
--   Entropy of the biased distribution and its quadratic deficit
-- statement:
--   Let $S\subseteq[N]$ have size $N/2\ge1$ and $0\le\varepsilon\le1/6$. Put $p=1/2+3\varepsilon$ and $q=1/2-3\varepsilon$. The biased distribution $\mathcal D_{S,\varepsilon}$ has entropy
--
--   $$
--   H(\mathcal D_{S,\varepsilon})=\log_2 N-\bigl[1-p\log_2(1/p)-q\log_2(1/q)\bigr],
--   $$
--
--   and there is an absolute constant $C>0$, independent of $N$, $S$, and $\varepsilon$, such that
--
--   $$
--   H(\mathcal D_{S,\varepsilon})\ge\log_2 N-C\varepsilon^2.
--   $$
--
--   This gives the per-sample entropy deficit used in the mutual-information bound. The endpoint $q=0$ follows the convention $0\log_2(1/0)=0$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 21, proof of Theorem 16, entropy display

import Mathlib
import Definitions.Def_WildeQIT_entropy
import Definitions.Def_ShadowTomography_ClassicalLB_biasedDist

namespace ShadowTomography.ClassicalLB

/-- The exact entropy expression on p. 21 and its uniform quadratic deficit. -/
theorem entropy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (S : Finset (Fin N)) (ε : ℝ),
      2 * S.card = N → 1 ≤ S.card → 0 ≤ ε → ε ≤ 1 / 6 →
      ∃ p : WildeQIT.FinDist (Fin N),
        (∀ x, p.prob x = biasedDist N S ε x) ∧
        WildeQIT.entropy p = Real.logb 2 N -
          (1 - (1 / 2 + 3 * ε) * Real.logb 2 (1 / (1 / 2 + 3 * ε)) -
            (1 / 2 - 3 * ε) * Real.logb 2 (1 / (1 / 2 - 3 * ε))) ∧
        Real.logb 2 N - C * ε ^ 2 ≤ WildeQIT.entropy p := by sorry

end ShadowTomography.ClassicalLB
