-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_lemma_5_1
-- name    : SignFreeOracle.Separation.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:30.36139+00:00
-- url     : https://prove2.me/theorems/c625f23e-2fbb-4ef1-a0b8-d37af2629696
-- title:
--   Lemma 5.1 (corrected: positive sampling budget) — arbitrary-witness label fixing
-- statement:
--   Let $2^m\ge16$, let $\pi\mapsto w_\pi\in\{0,1\}^p$ be an arbitrary map on all labellings, let $0<\gamma\le1$, and let $t\ge1$ be an integer. There are distributions $D_w$ supported on injective partial labellings of at most $t$ vertices, simultaneously for all algorithms and all query budgets. Draw $\pi$ uniformly, then $\sigma\sim D_{w_\pi}$, then $\pi'$ uniformly extending $\sigma$. Every algorithm $B$ with at most $q$ forward or inverse permutation queries satisfies
--   $$\left|\Pr[B^\pi(w_\pi)=1]-\Pr[B^{\pi'}(w_\pi)=1]\right|\le\frac{2(p+\log_2(1/\gamma))q}{t}+\gamma.$$
--   The same witness is retained in both experiments. No upper bound on $t$ is imposed, and $\gamma=1$ is permitted. This converts arbitrary information about a random labelling into an algorithm-independent partial-labelling experiment.
--
--   Differences from the source:
--   - correction: t is any natural number in a denominator → t is a positive natural number; reason: t=0 makes the displayed quotient undefined
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Lemma 5.1, p. 15 (PDF p. 15)

import Definitions.Def_SignFreeOracle_Separation_Experiments

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- The t=0 quotient in the printed statement is undefined; t is positive here. -/
theorem lemma_5_1 (m p t : ℕ) (hm : 16 ≤ 2 ^ m) (ht : 1 ≤ t)
    (w : Equiv.Perm (Fin (2 ^ m)) → Bits p) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ D : Bits p → PMF (PartialLabel (2 ^ m)), PresamplingGood w γ t D := by sorry

end SignFreeOracle.Separation
