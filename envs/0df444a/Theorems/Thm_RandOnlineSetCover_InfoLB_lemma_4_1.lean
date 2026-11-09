-- Prove2me | Theorems.Thm_RandOnlineSetCover_InfoLB_lemma_4_1
-- name    : RandOnlineSetCover.InfoLB.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:25.323895+00:00
-- url     : https://prove2.me/theorems/6452c61a-95aa-4aea-9c9a-5fa4bc6bc3e1
-- title:
--   Lemma 4.1 — binary-tree amplification
-- statement:
--   Let $q\ge1$ and let $m,n,L$ be nonnegative integers. Suppose $D$ is a distribution on instances with $m$ labeled sets and exactly $n$ requests such that $\operatorname{Opt}(I)\le L$ almost surely, and suppose every deterministic online algorithm has expected cost at least $\beta\in\mathbb R$ under $D$. There is a distribution $D_{\rm fin}$ on instances with exactly $qn$ requests and $2^{q-1}m^q$ labeled sets such that
--
--   $$
--   \operatorname{Opt}(I_{\rm fin})\le L\quad(D_{\rm fin}\text{-almost surely}),\qquad
--   \mathbb E_{I_{\rm fin}\sim D_{\rm fin}}[|A(I_{\rm fin})|]\ge\frac{q\beta}{2}
--   \quad\text{for every deterministic online algorithm }A.
--   $$
--
--   The bound retains the inner offline optimum while increasing the cost lower bound with the number of outer levels. The final distribution is existential; no amplification conclusion is assumed in its input data.
--
--   Differences from the source:
--   - encoding: an outer tree with q levels including the root and probability-one optimum bounds → the explicit domain q ≥ 1, natural counts, real β, and supportwise PMF bounds; reason: the level convention excludes q = 0 where 2^(q-1) is not the intended leaf count; finite PMFs preserve all distributions at fixed sizes
-- source:
--   Roie Levin, STOC 2027 submission #400 (October 2026), Lemma 4.1, p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/400.pdf

import Mathlib
import Definitions.Def_RandOnlineSetCover_InfoLB_Model

namespace RandOnlineSetCover.InfoLB

theorem lemma_4_1 (q m n L : ℕ) (hq : 1 ≤ q) (β : ℝ)
    (D : InstanceDistribution m n) (hopt : OptBound D L)
    (hcost : ∀ A : DetAlg m n, β ≤ distributionCost D A) :
    ∃ Dfin : InstanceDistribution (2 ^ (q - 1) * m ^ q) (q * n),
      OptBound Dfin L ∧
      ∀ A : DetAlg (2 ^ (q - 1) * m ^ q) (q * n),
        (q : ℝ) * β / 2 ≤ distributionCost Dfin A := by sorry

end RandOnlineSetCover.InfoLB
