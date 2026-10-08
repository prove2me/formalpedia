-- Prove2me | Theorems.Thm_WeightedMajority_Anomalies_first_stage
-- name    : WeightedMajority.Anomalies.first_stage
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:24.641974+00:00
-- url     : https://prove2.me/theorems/12e374d1-ddd4-4101-920d-a564ed32c946
-- title:
--   First stage of the adversary in Theorem 8.1: k − 1 forced mistakes and two consistent functions that disagree
-- statement:
--   Let $F$ be a class of $\{0,1\}$-valued functions on a domain $X$, and let $k \ge 1$. Suppose $F$ has a complete $k$-mistake tree, i.e. a complete binary tree of depth $k$ whose internal nodes are labelled by instances of $X$ such that every root-to-leaf labelling $(y_1,\dots,y_k) \in \{0,1\}^k$ is realized by some $f \in F$ along the path it determines ($F$ shatters the tree).
--
--   Then for every deterministic on-line prediction algorithm $A$ there exist a sequence of $k-1$ trials $(x_1,y_1),\dots,(x_{k-1},y_{k-1})$, an instance $x \in X$ and two functions $f_1, f_2 \in F$ such that
--   1. $A$ is wrong at every one of the $k-1$ trials: its prediction at trial $t$, made from $(x_1,y_1),\dots,(x_{t-1},y_{t-1})$ and $x_t$, differs from $y_t$;
--   2. $f_1$ and $f_2$ are both consistent with all $k-1$ trials: $f_i(x_t) = y_t$ for every $t \le k-1$ and $i = 1, 2$;
--   3. $$f_1(x) \ne f_2(x).$$
--
--   This is the first stage of the adversary in the lower bound $\mathrm{opt}(F,\eta) \ge \mathrm{opt}(F,0) + 2\eta$: after it, the adversary can repeat the instance $x$ with labels that disagree with the algorithm, keeping one of $f_1, f_2$ within the anomaly budget.
--
--   **Formalization Note** A complete $k$-mistake tree is encoded by the published predicate `ShattersTree F k v` of `UnderstandingML_Online`, in which a node is the list of labels on the path leading to it. Trials are indexed by `Fin (k - 1)`; since $k \ge 1$ the truncated subtraction is exact.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 251, Section 8, proof of Theorem 8.1 (end of the first stage)

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_WeightedMajority_Anomalies_Opt

namespace WeightedMajority.Anomalies

open UnderstandingML

/-- The first stage of the adversary in the proof of Theorem 8.1 (§8, p. 251). If `F` has a
complete `k`-mistake tree (an `F`-shattered tree of depth `k`), `k ≥ 1`, then against any
deterministic algorithm `A` there is a sequence of `k − 1` trials on which `A` is wrong at every
trial, together with an instance `x` and two functions `f₁, f₂ ∈ F`, both consistent with all
`k − 1` trials, such that `f₁ x ≠ f₂ x`. -/
theorem first_stage {X : Type*} (F : Set (X → Bool)) (A : OnlineAlg X Bool) (k : ℕ)
    (hk : 1 ≤ k) (htree : ∃ v : List Bool → X, ShattersTree F k v) :
    ∃ S : Fin (k - 1) → X × Bool,
      (∀ t : Fin (k - 1), A (history S t) (S t).1 ≠ (S t).2) ∧
      ∃ f₁ ∈ F, ∃ f₂ ∈ F, ∃ x : X,
        (∀ t : Fin (k - 1), f₁ (S t).1 = (S t).2) ∧
        (∀ t : Fin (k - 1), f₂ (S t).1 = (S t).2) ∧
        f₁ x ≠ f₂ x := by sorry

end WeightedMajority.Anomalies
