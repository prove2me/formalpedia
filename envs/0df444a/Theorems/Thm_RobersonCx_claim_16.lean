-- Prove2me | Theorems.Thm_RobersonCx_claim_16
-- name    : RobersonCx.claim_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:35.227058+00:00
-- url     : https://prove2.me/theorems/76727365-cb2c-4d87-98f3-2f3ac249488a
-- title:
--   Claim 16 — in $D^{(r)}_n-\{n-1,0\}$, a component of $G-S$ containing a block is large
-- statement:
--   Let $r\ge2$, $n>4r^2-2r$, $f=\{n-1,0\}$ and $G=D^{(r)}_n-f$. A **block** is a set $\{a,a+1,\dots,a+r-1\}$ with $a$ an integer, $0\le a\le n-r$ (blocks do not wrap from $n-1$ to $0$). Let $S\subseteq V(G)$ with $|S|\le 2r-1$. Then every connected component of $G-S$ containing a block has more than $n/2$ vertices.
--
--   This is the component estimate inside the proof of Lemma 15 (the setting is that of the proof, where $f$ is rotated to $\{n-1,0\}$).
--
--   Differences from the source:
--   - encoding: $n>4r^2-2r$ → $4r^2<n+2r$ in $\mathbb N$; reason: avoids natural-number subtraction; same instances
--   - encoding: more than $n/2$ vertices → $n<2|C|$ in $\mathbb N$; reason: avoids division; same instances
--   - encoding: block $\{a,\dots,a+r-1\}$, $0\le a\le n-r$ → the casts of $a,\dots,a+r-1$ into `ZMod n` with $a+r\le n$; reason: vertices of $D^{(r)}_n$ are residues; same sets
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Claim 16 in the proof of Lemma 15, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_RobersonCx_circulantD

set_option autoImplicit false

namespace RobersonCx

/-- Claim 16 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. A.4, pp.14–15 (PDF pp.16–17)), inside the proof of Lemma 15. Setting: `r ≥ 2`,
`n > 4r² − 2r`, `f = {n − 1, 0}` and `G = D^(r)_n − f`; a block is a set `{a, a + 1, …, a + r − 1}` for an integer `a`
with `0 ≤ a ≤ n − r` (blocks do not wrap). Claim: let `S ⊆ V(G)` with `|S| ≤ 2r − 1`. Every component of `G − S`
containing a block has more than `n/2` vertices.

**Formalization Note** `n > 4r² − 2r` is written `4r² < n + 2r` (no natural-number subtraction). A block is
`{a, …, a + r − 1}` cast into `ZMod n` with `a + r ≤ n`. A component of `G − S` is a connected component of the
induced subgraph on the complement of `S`, identified with its vertex set; "more than `n/2`" is `n < 2|C|`. -/
theorem claim_16 (r n : ℕ) (hr : 2 ≤ r) (hn : 4 * r ^ 2 < n + 2 * r) (S : Set (ZMod n))
    (hS : S.ncard ≤ 2 * r - 1)
    (C : (((circulantD n r).deleteEdges {s(((n - 1 : ℕ) : ZMod n), 0)}).induce Sᶜ).ConnectedComponent)
    (hC : ∃ a : ℕ, a + r ≤ n ∧ ∀ j < r, ((a + j : ℕ) : ZMod n) ∈ Subtype.val '' C.supp) :
    n < 2 * (Subtype.val '' C.supp).ncard := by sorry

end RobersonCx
