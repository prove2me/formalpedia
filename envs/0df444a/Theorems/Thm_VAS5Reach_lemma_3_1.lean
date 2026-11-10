-- Prove2me | Theorems.Thm_VAS5Reach_lemma_3_1
-- name    : VAS5Reach.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:34.281205+00:00
-- url     : https://prove2.me/theorems/eca2f9d7-b7ff-4faf-a098-101826ab2c27
-- title:
--   Lemma 3.1 (Rackoff) — covering runs of length $< N^{O((d+1)!)}$, $N = \max\{2, |Q|, \|T\|, \|z\|\}$
-- statement:
--   There is a constant $c$ such that the following holds. Let $V = (Q, T)$ be a $d$-VASS. If $q(z)$ is coverable from $p(x)$, that is $p(x) \xrightarrow{*} q(z')$ for some $z' \ge z$, then there is such a covering run ending at state $q$ of length less than
--   $$
--   N^{c\,(d+1)!}, \qquad N := \max\{2, |Q|, \|T\|, \|z\|\}.
--   $$
--   The bound does not depend on $x$. This is [Rac78, Theorem 3.5]; the proof is in the cited work.
--
--   Differences from the source:
--   - encoding: N^{O((d+1)!)} → N^{c·(d+1)!} with one constant c quantified before d and every instance; reason: O((d+1)!) ≤ c·(d+1)! for a suitable c
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 3.1, p.16 (PDF p.18); cited from [Rac78, Theorem 3.5]

import Mathlib
import Definitions.Def_VAS5Reach_supNorm
import Definitions.Def_VAS5Reach_VASS
import Definitions.Def_VAS5Reach_VASS_IsRun

namespace VAS5Reach

/-- **Lemma 3.1 ([Rac78, Theorem 3.5]).** Let `V = (Q, T)` be a `d`-VASS. If `q(z)` is coverable
from `p(x)`, there is a covering run ending at state `q` of length less than `N^{O((d+1)!)}`, where
`N := max{2, |Q|, ∥T∥, ∥z∥}`.

Here `q(z)` is coverable from `p(x)` if `p(x) −∗→ q(z′)` for some `z′ ≥ z`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 3.1 and the definition before it, printed p. 16 (PDF p. 18). Cited from
[Rac78, Theorem 3.5]; the proof is not in this paper.

**Formalization Note** `d = Fintype.card ι`; `O((d+1)!)` is `c·(d+1)!` with one `c` quantified
before `d` and every instance. The bound does not depend on `x`. -/
theorem lemma_3_1 :
    ∃ c : ℕ, ∀ {ι Q : Type} [Fintype ι] (V : VASS Q ι) (p q : Q) (x z : ι → ℕ),
      (∃ z', z ≤ z' ∧ V.Reach p x q z') →
      ∃ (π : List (Q × (ι → ℤ) × Q)) (z' : ι → ℕ), z ≤ z' ∧ V.IsRun p x π q z' ∧
        π.length < (max 2 (max V.states.card (max V.normTrans (supNormN z)))) ^
          (c * (Fintype.card ι + 1).factorial) := by sorry

end VAS5Reach
