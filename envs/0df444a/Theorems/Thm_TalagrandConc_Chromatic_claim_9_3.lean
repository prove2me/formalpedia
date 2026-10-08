-- Prove2me | Theorems.Thm_TalagrandConc_Chromatic_claim_9_3
-- name    : TalagrandConc.Chromatic.claim_9_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:13.792986+00:00
-- url     : https://prove2.me/theorems/03193c4f-b3d7-4639-9b7e-7621a3a37166
-- title:
--   Proof of Theorem 9.1, Eq. (9.3) — $\omega\in B\Rightarrow\chi(G(\omega),m)\ge a-k$
-- statement:
--   Fix integers $n,m,k\ge0$, a real $t>0$ and an integer $a$. On the vertex-exposure space $\Omega'=\prod_j\{0,1\}^{j-1}$, let $A$ be the set of $\omega$ for which
--   $$\chi(G(\omega),m)\ge a\quad\text{and}\quad\sup\{\chi(G(\omega),F);\ F\subset V,\ \operatorname{card}F\le t\sqrt m\}\le k,$$
--   and let $B$ be the set of $\omega$ such that for every family of nonnegative weights $(\alpha_j)$ there is $\omega'\in A$ with
--   $$\sum_j\alpha_j\,1_{\{\omega_j\ne\omega'_j\}}\le t\sqrt{\textstyle\sum_j\alpha_j^2}.$$
--   Then every $\omega\in B$ satisfies
--   $$\chi(G(\omega),m)\ge a-k.$$
--
--   This is the deterministic half of the proof of Theorem 9.1: combined with the bound $P(B)\ge1-e^{-t^2/8}$ that Theorem 4.1.1 and Lemma 4.1.2 give when $P(A)\ge e^{-t^2/8}$, it yields the lower tail of $\chi(G(n,p),m)$. The point is that $\Omega'$ has one coordinate per vertex, so changing the coordinates of a set $J$ of vertices only changes edges with an endpoint in $J$.
--
--   **Formalization Note** The statement involves no probability. $\chi(G(\omega),m)$ is $+\infty$ when $m>n$, in which case the conclusion holds trivially; comparisons with the integer $a-k$ are made in `WithTop ℤ`.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 164, proof of Theorem 9.1, Eq. (9.3) (set A defined on p. 163)

import Mathlib
import Definitions.Def_TalagrandConc_Chromatic_Basic

open MeasureTheory
open scoped Classical

namespace TalagrandConc.Chromatic

theorem claim_9_3 (n m k : ℕ) (t : ℝ) (ht : 0 < t) (a : ℤ) (ω : VxSpace n)
    (hω : ω ∈ setB (setA n m k t a) t) :
    (((a - k : ℤ)) : WithTop ℤ) ≤ chiMZ (vxGraph ω) m := by sorry

end TalagrandConc.Chromatic
