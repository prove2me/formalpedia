-- Prove2me | Theorems.Thm_RendezvousKn_Sym_assertion_1
-- name    : RendezvousKn.Sym.assertion_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:59.010764+00:00
-- url     : https://prove2.me/theorems/a084052b-161c-48c0-a949-97911400cf5c
-- title:
--   Assertion 1, p. 7 — E X_eX_f ≤ 1/(n(n−1)), E X_eX_fX_g ≤ 1/(n)_3, E X_eX_fX_gX_h ≤ 1/(n)_4 for pairwise different pairs
-- statement:
--   Fix $n\ge2$ and let $\pi$ be a uniformly random permutation of $[n]$. For a pair $e=(i,j)\in[n]\times[n]$, let $X_e$ be the indicator of $\pi(i)=j$. Then, for pairwise different pairs $e,f,g,h$ of $[n]\times[n]$:
--   $$\mathbb E\,X_eX_f\le\frac1{n(n-1)},\qquad \mathbb E\,X_eX_fX_g\le\frac1{n(n-1)(n-2)},\qquad \mathbb E\,X_eX_fX_gX_h\le\frac1{n(n-1)(n-2)(n-3)}.$$
--   Each bound requires only its own pairs to be pairwise different.
--
--   These joint-moment bounds feed the fourth-moment bound of Assertion 2.
--
--   Differences from the source:
--   - generalization: pairwise different pairs e, f, g, h ∈ F (F the pair set of two tactics) → pairwise different pairs of Fin n × Fin n; each clause assumes only its own pairs pairwise different; reason: F ⊆ [n] × [n], so the source's assertion is the special case of pairs taken from F; the paper's proof never uses membership in F
--   - encoding: 1/(n(n−1)(n−2)) and 1/(n(n−1)(n−2)(n−3)), undefined for n = 2 resp. n ≤ 3 → real division with 1/0 = 0; reason: in those cases no three (four) pairwise different pairs can be pairwise disjoint, so the product of indicators is identically 0 and the Lean bound 0 is exact; for the n where the source's expression is defined nothing changes
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 7 (PDF 8), Assertion 1 (proof p. 8, PDF 9)

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem assertion_1 (n : ℕ) (hn : 2 ≤ n) :
    (∀ e f : Fin n × Fin n, e ≠ f →
      avgPerm n (fun π => matchInd e π * matchInd f π) ≤ 1 / ((n : ℝ) * (n - 1))) ∧
    (∀ e f g : Fin n × Fin n, e ≠ f → e ≠ g → f ≠ g →
      avgPerm n (fun π => matchInd e π * matchInd f π * matchInd g π) ≤
        1 / ((n : ℝ) * (n - 1) * (n - 2))) ∧
    (∀ e f g h : Fin n × Fin n, e ≠ f → e ≠ g → e ≠ h → f ≠ g → f ≠ h → g ≠ h →
      avgPerm n (fun π => matchInd e π * matchInd f π * matchInd g π * matchInd h π) ≤
        1 / ((n : ℝ) * (n - 1) * (n - 2) * (n - 3))) := by sorry

end RendezvousKn.Sym
