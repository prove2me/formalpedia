-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_lemma_4_2
-- name    : PooledTestingAdaptivity.Gap.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:17.549524+00:00
-- url     : https://prove2.me/theorems/fe5ca677-5ba1-4b0f-a746-1f462a2fd426
-- title:
--   Lemma 4.2 — Normalization
-- statement:
--   Fix an instance $J$, a test budget $B\ge0$ and a nonempty downward-closed feasible family $\mathcal F$. There is a normalization map $N$ on finite deterministic policies such that, whenever $\pi$ is feasible, $N(\pi)$ is feasible and normalized and
--
--   $$C(P_{N(\pi)}(x),x)=C(P_\pi(x),x)\qquad\text{for every health profile }x.$$
--
--   Every pool below the negative child of a node in $N(\pi)$ is disjoint from that node's pool, including on inconsistent branches. Thus both clearance preservation and the full syntactic conclusion are asserted. No equality of realized allocation lengths is required. Applying $N$ to the tree selected by each random seed gives the same cleared set for every seed and every profile under a randomized policy. This is the normal form used by the comparison results.
--
--   Differences from the source:
--   - encoding: people indexed by [n] and finite pool-labelled binary policies → people indexed by Fin n, health in Bool, and the published QTree with unit-valued stop leaves; reason: reindexing and tree constructors represent exactly the same health profiles, histories and policies
--   - encoding: every feasible policy has a normalized policy → one map N chooses such a normalized tree for each feasible deterministic tree; reason: classical choice packages the same existential witnesses into a function; composition with any health-independent sampled tree preserves clearance with the same seed
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Lemma 4.2, printed p. 12, PDF p. 13; proof printed pp. 12–13, PDF pp. 13–14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1397.pdf

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Policies

namespace PooledTestingAdaptivity.Gap

/-- Lemma 4.2, printed p.12 / PDF p.13: clearance preservation is pointwise.
Applying this normalization to each health-independent seed covers randomized policies. -/
theorem lemma_4_2 {n B : ℕ} (J : Instance n) (F : FeasibleFamily J B)
    (hF : DownwardClosed F) :
    ∃ N : Policy n → Policy n, ∀ π : Policy n, Feasible F π →
      Feasible F (N π) ∧ Normalized (N π) ∧
      (∀ x : Profile n, cleared (run (N π) x) x = cleared (run π x) x) ∧
      SyntacticallyNormalized (N π) := by sorry

end PooledTestingAdaptivity.Gap
