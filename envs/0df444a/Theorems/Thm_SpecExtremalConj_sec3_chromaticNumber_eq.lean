-- Prove2me | Theorems.Thm_SpecExtremalConj_sec3_chromaticNumber_eq
-- name    : SpecExtremalConj.sec3_chromaticNumber_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:11:18.444049+00:00
-- url     : https://prove2.me/theorems/b2bd6b59-eef9-4692-a7c0-732e2fd985e8
-- title:
--   §3 (p. 4): $\chi(F)=r+1$ in the §3 setting
-- statement:
--   Throughout, $r\ge2$ and $F$ is a finite graph such that, for every $n\ge n_1$, every graph of $\mathrm{Ex}(n,F)$ is a relabelled $T_{n,r}$ plus exactly $a$ edges (the standing assumption of Section 3). "$G$" denotes any $F$-free graph on $n$ vertices of maximum spectral radius ($G\in\mathrm{Ex}_{sp}(n,F)$). Suppose moreover that $F$ has at least one edge. Then
--
--   $$\chi(F)=r+1.$$
--
--   The paper derives this from $\mathrm{ex}(n,F)=e(T_{n,r})+a$, the Erdős–Stone–Simonovits theorem (1) and $(1-\frac1r)\frac{n^2}{2}-\frac r8\le e(T_{n,r})\le(1-\frac1r)\frac{n^2}{2}$. It makes the spectral stability result (Corollary 2.6) applicable to $F$.
--
--   Differences from the source:
--   - encoding: F any graph (with (1) applied to it) → F ≠ ⊥ (F has an edge); reason: for edgeless F there is no F-free graph on n ≥ |V(F)| vertices, so the setting holds vacuously, χ(F) ≤ 1 and 1 − 1/(χ(F) − 1) in (1) is undefined; the condition excludes only this undefined case
--   - reading: §3 standing assumption: the graphs in Ex(n, F) are obtained from T_{n,r} by adding a edges (n large) → IsTuranPlusConst F r a n₁: for every n ≥ n₁, every member of Ex(n, F) contains a relabelled spanning T_{n,r} and has e(T_{n,r}) + a edges; reason: the paper uses the assumption only at large orders; a threshold n₁ is the weaker hypothesis, hence the stronger statement
--   - encoding: "obtained from T_{n,r} by adding edges" → contains a relabelled spanning copy of turanGraph n r (ContainsSpanningTuran), with the number of added edges read off the edge count; reason: graphs are taken up to isomorphism; a graph contains a spanning T_{n,r} with k further edges exactly when it is T_{n,r} plus k edges
--   - encoding: an n-vertex graph → a simple graph on Fin n; reason: the spectral radius, F-freeness and edge counts are invariant under relabelling, so every n-vertex graph is an instance
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §3, p. 4 (unnumbered: "which implies that χ(F) = r + 1 by (1) …")

import Mathlib
import Definitions.Def_SpecExtremalConj_IsTuranPlusConst
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **χ(F) = r + 1 in the §3 setting.** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §3, p. 4 (unnumbered): "Then ex(n, F) = e(T_{n,r}) + a,
which implies that χ(F) = r + 1 by (1) and the fact (1 − 1/r)n²/2 − r/8 ≤ e(T_{n,r}) ≤ (1 − 1/r)n²/2."
Here (1) is the Erdős–Stone–Simonovits theorem (p. 1).

If `r ≥ 2`, `F` has at least one edge, and for every `n ≥ n₁` every graph of Ex(n, F) is a
relabelled T_{n,r} plus exactly `a` edges, then the chromatic number of `F` is `r + 1`.

**Formalization Note.** `F ≠ ⊥` (F has an edge) is added: for an edgeless F there is no F-free
graph on `n ≥ |V(F)|` vertices, so the hypothesis holds vacuously while χ(F) ≤ 1, and the
quantity 1 − 1/(χ(F) − 1) in (1) is undefined. `chromaticNumber` is `ℕ∞`-valued. -/
theorem sec3_chromaticNumber_eq {W : Type*} [Fintype W] (F : SimpleGraph W) (r a n₁ : ℕ) (hr : 2 ≤ r)
    (hF : IsTuranPlusConst F r a n₁)
    (hF0 : F ≠ ⊥) : F.chromaticNumber = ((r + 1 : ℕ) : ℕ∞) := by sorry

end SpecExtremalConj
