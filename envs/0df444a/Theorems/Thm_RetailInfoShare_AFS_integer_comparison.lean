-- Prove2me | Theorems.Thm_RetailInfoShare_AFS_integer_comparison
-- name    : RetailInfoShare.AFS.integer_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:12.273277+00:00
-- url     : https://prove2.me/theorems/28f70b7e-22bb-4fa9-8e33-5b9f48ff3185
-- title:
--   §4, p. 18 — the best integer group size is ⌊min{2/b−1, N}⌋ or ⌈min{2/b−1, N}⌉
-- statement:
--   Assume the standing assumptions, and let
--   $$G(K) = \frac{\alpha K \sigma^2}{[2 + b(K-1)]^2\left(\sigma + \frac tN\right)}, \qquad m = \min\Big\{\frac2b - 1, N\Big\}.$$
--   Then:
--   1. some $K \in \{\lfloor m \rfloor, \lceil m \rceil\}$ with $K \le N$ maximizes $G$ over $\{0, 1, \dots, N\}$;
--   2. every maximizer of $G$ over $\{0, 1, \dots, N\}$ lies in $\{\lfloor m \rfloor, \lceil m \rceil\}$.
--
--   This is the purely arithmetic step that turns the real optimum $\min\{2/b-1,N\}$ into the integer group size of Proposition 2.
-- source:
--   Liu, Zhang & Zhang, Information Sharing on Retail Platforms, SSRN 3258109 (PDF of 2023-03-01), §4, p. 18, 'So we need to compare the expected profit at the two nearest integers around min{2/b − 1, N} …'

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS

theorem integer_comparison (P : Params) (hP : P.Standing) :
    (∃ K : ℕ, (K = ⌊mStar P⌋₊ ∨ K = ⌈mStar P⌉₊) ∧ K ≤ P.N ∧
        ∀ K' : ℕ, K' ≤ P.N → sharingGain P K' ≤ sharingGain P K) ∧
    ∀ K : ℕ, K ≤ P.N → (∀ K' : ℕ, K' ≤ P.N → sharingGain P K' ≤ sharingGain P K) →
      K = ⌊mStar P⌋₊ ∨ K = ⌈mStar P⌉₊ := by sorry

end RetailInfoShare.AFS
