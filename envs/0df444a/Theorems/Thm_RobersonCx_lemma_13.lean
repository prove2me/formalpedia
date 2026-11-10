-- Prove2me | Theorems.Thm_RobersonCx_lemma_13
-- name    : RobersonCx.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:55.824124+00:00
-- url     : https://prove2.me/theorems/3ca9ab94-81d9-48ff-a6cd-cbf83778f109
-- title:
--   Lemma 13 — pathwidth bounds for $D^{(r)}_n$, $D^{(r)}_n-W$ and $D^{(r)}_n-e$
-- statement:
--   Let $r\ge2$ and $n>2r$. Then:
--
--   1. $\mathrm{pw}(D^{(r)}_n)\le 2r$;
--   2. if $W=\{a,a+1,\dots,a+r-1\}$ consists of $r$ consecutive vertices in the numerical cyclic order, then $\mathrm{pw}(D^{(r)}_n-W)\le r$;
--   3. if $e=\{i,i+r\}$ is a long edge, then $\mathrm{pw}(D^{(r)}_n-e)\le 2r-1$.
--
--   Here $G-W$ is the subgraph induced on $V(G)\setminus W$ and $G-e$ deletes the edge $e$. These are the host-side bounds that feed hypotheses (ii) and (iii) of Lemma 19.
--
--   Differences from the source:
--   - encoding: $\mathrm{pw}(\cdot)\le k$ → `PwLE · k`: a `GaussianSweep.IsPathDecomposition` with bags of size at most $k+1$; reason: a path decomposition indexed along the path; same notion
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Lemma 13, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RobersonCx_circulantD
import Definitions.Def_RobersonCx_TwLE

set_option autoImplicit false

namespace RobersonCx

/-- Lemma 13 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. A.3, p.13 (PDF p.15)). Let `r ≥ 2` and `n > 2r`. Then: (i) `pw(D^(r)_n) ≤ 2r`; (ii) if `W`
consists of `r` consecutive vertices in the numerical cyclic order, then `pw(D^(r)_n − W) ≤ r`; (iii) if `e` is a
long edge, then `pw(D^(r)_n − e) ≤ 2r − 1`.

**Formalization Note** `W = {a, a + 1, …, a + r − 1}` in `ZMod n`; `G − W` is the induced subgraph on the
complement; a long edge is `{i, i + r}`; `G − e` is `deleteEdges {e}`. -/
theorem lemma_13 (r n : ℕ) (hr : 2 ≤ r) (hn : 2 * r < n) :
    PwLE (circulantD n r) (2 * r) ∧
    (∀ a : ZMod n,
      PwLE ((circulantD n r).induce ({x | ∃ j < r, x = a + (j : ZMod n)} : Set (ZMod n))ᶜ) r) ∧
    (∀ i : ZMod n, PwLE ((circulantD n r).deleteEdges {s(i, i + (r : ZMod n))}) (2 * r - 1)) := by sorry

end RobersonCx
