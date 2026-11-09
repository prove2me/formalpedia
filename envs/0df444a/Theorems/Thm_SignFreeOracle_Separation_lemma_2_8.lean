-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_lemma_2_8
-- name    : SignFreeOracle.Separation.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:52.017583+00:00
-- url     : https://prove2.me/theorems/38140138-84e2-4664-b5f1-6fa1e908362d
-- title:
--   Lemma 2.8 — closure size and every legal run length
-- statement:
--   Let $U$ contain $t\ge1$ vertices of a finite simple graph $G$, and let the integer $r\ge2$. If every cycle has length at least $g$ and
--   $$g\ge4r\log_2(2rt)+4,$$
--   then every legal run of the path-addition procedure has fewer than $2t$ additions, and its least closed terminal set satisfies
--   $$|\operatorname{clos}_{G,r}(U)|<2rt.$$
--   Both inequalities are strict. Runs can choose any eligible simple path at each step. The quantitative conclusions are absent from the closure definition. This bounds both the cost and the set produced by every allowed addition order.
--
--   Differences from the source:
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - encoding: terminal set produced by any legal path-addition order → least path-closed superset, together with the bound for every legal run; reason: these are the same closure; termination follows from finite strict growth
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Lemma 2.8, p. 8 (PDF p. 8)

import Definitions.Def_SignFreeOracle_Separation_Graph

set_option autoImplicit false

namespace SignFreeOracle.Separation

theorem lemma_2_8 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (U : Finset V) (r : ℕ) (g : ℝ) (hU : 1 ≤ U.card) (hr : 2 ≤ r)
    (hg : 4 * r * Real.logb 2 (2 * r * (U.card : ℝ)) + 4 ≤ g)
    (hgir : GirthAtLeast G g) :
    (∀ steps : List (Finset V), (U :: steps).IsChain (ClosureStep G r) →
      steps.length < 2 * U.card) ∧
    (closure G r (U : Set V)).ncard < 2 * r * U.card := by sorry

end SignFreeOracle.Separation
