-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_proposition_4_6
-- name    : PooledTestingAdaptivity.Gap.proposition_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:27.655126+00:00
-- url     : https://prove2.me/theorems/762fb532-cf57-4349-8e7a-d4468b3d6989
-- title:
--   Proposition 4.6 — Per-individual comparison under product priors
-- statement:
--   Let $J$ have independent health bits with the same product prior for two independent profiles $X$ and $Y$. For every normalized policy $\pi$ and every person $i$,
--
--   $$\mathbb E[d_i(X)]\le2\mathbb E[h_i(P_\pi(X),Y)].$$
--
--   The expectation on the right is over both independent profiles; $h_i$ already averages the independent occurrence coins. Priors may equal one. The statement concerns every individual and requires no positive welfare. It is the exact Equation (10), at the product-prior level, used in the welfare comparison.
--
--   **Formalization Note** Each expectation is its finite sum with product masses, and the two independent profiles are represented by nested such sums.
--
--   Differences from the source:
--   - encoding: people indexed by [n] and finite pool-labelled binary policies → people indexed by Fin n, health in Bool, and the published QTree with unit-valued stop leaves; reason: reindexing and tree constructors represent exactly the same health profiles, histories and policies
--   - encoding: probability over independent fair coins for individual occurrences → uniform finite average over test-position/person bits, with unused bits outside each pool; reason: dummy bits cancel from the average; each real occurrence has its own independent fair bit
--   - encoding: expectations of independent profiles X and Y from the product prior → finite sums with mass μ_J(x), and μ_J(x)μ_J(y) for the paired expectation; reason: the product weights give exactly the specified independent copies, including zero-mass profiles
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Proposition 4.6, printed p. 17, PDF p. 18; Eq. (10), printed p. 13, PDF p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1397.pdf

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_HalfThinning

namespace PooledTestingAdaptivity.Gap

/-- Proposition 4.6, printed p.17 / PDF p.18, including Eq.(10).
The nested sums use independent virtual and evaluation profiles. -/
theorem proposition_4_6 {n : ℕ} (J : Instance n) (π : Policy n)
    (hπ : Normalized π) (i : Fin n) :
    expectation J (clearanceIndicator π i) ≤
      2 * expectation J (fun x => expectation J (fun y =>
        thinningClearance (run π x) y i)) := by sorry

end PooledTestingAdaptivity.Gap
