-- Prove2me | Theorems.Thm_RobersonCx_lemma_8
-- name    : RobersonCx.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:36.537516+00:00
-- url     : https://prove2.me/theorems/14499297-0c7c-4034-b13c-a91fdfc12d52
-- title:
--   Lemma 8 — rotations of $D^{(r)}_{qm}$, $B^{(r)}_{qm}$ of order $m$ with quotients $D^{(r)}_q$, $B^{(r)}_q$
-- statement:
--   Let $r\ge2$ (the standing assumption of §4.1). For every integer $q>2r$ and every positive integer $m$, the graphs $D^{(r)}_{qm}$ and $B^{(r)}_{qm}$ have automorphisms $\sigma$ of order $m$ whose orbit quotients are isomorphic to $D^{(r)}_q$ and $B^{(r)}_q$, respectively:
--   $$D^{(r)}_{qm}/\langle\sigma\rangle\cong D^{(r)}_q,\qquad B^{(r)}_{qm}/\langle\sigma'\rangle\cong B^{(r)}_q.$$
--
--   These automorphisms (the rotation $i\mapsto i+q$) provide, for $m=p$ prime, the graphs $F_p$ required in Corollary 7.
--
--   Differences from the source:
--   - encoding: orbit quotient is $D^{(r)}_q$ / $B^{(r)}_q$ → `QuotIsoTo` (isomorphism of the loop-allowing quotient onto the simple graph); reason: same meaning; the quotients are loopless
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Lemma 8, p.9 (PDF p.11); standing assumption r ≥ 2 of §4.1, p.8

import Mathlib
import Definitions.Def_RobersonCx_QuotIsoTo
import Definitions.Def_RobersonCx_circulantD

set_option autoImplicit false

namespace RobersonCx

/-- Lemma 8 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §4.1, p.9 (PDF p.11)). For every integer `q > 2r` and every positive integer `m`, the graphs
`D^(r)_{qm}` and `B^(r)_{qm}` have automorphisms of order `m` whose orbit quotients are `D^(r)_q` and `B^(r)_q`,
respectively.

**Formalization Note** `r ≥ 2` is the standing assumption of §4.1 ("Fix integers r ≥ 2 and n > 2r", p.8).
"Orbit quotient is `D^(r)_q`" is `QuotIsoTo` (an isomorphism of the loop-allowing quotient onto the simple
graph). -/
theorem lemma_8 (r q m : ℕ) (hr : 2 ≤ r) (hq : 2 * r < q) (hm : 0 < m) :
    (∃ σ : circulantD (q * m) r ≃g circulantD (q * m) r,
      orderOf σ = m ∧ QuotIsoTo (circulantD (q * m) r) σ.toEquiv (circulantD q r)) ∧
    (∃ σ : splitB (q * m) r ≃g splitB (q * m) r,
      orderOf σ = m ∧ QuotIsoTo (splitB (q * m) r) σ.toEquiv (splitB q r)) := by sorry

end RobersonCx
