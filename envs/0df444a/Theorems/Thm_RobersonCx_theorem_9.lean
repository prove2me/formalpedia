-- Prove2me | Theorems.Thm_RobersonCx_theorem_9
-- name    : RobersonCx.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:45.738553+00:00
-- url     : https://prove2.me/theorems/af686284-a30e-4192-9769-360582e575f6
-- title:
--   Theorem 9 — $D^{(r)}_q\not\preccurlyeq_{\mathrm m}D^{(r)}_{qm}$, $B^{(r)}_q\not\preccurlyeq_{\mathrm m}B^{(r)}_{qm}$, $B^{(r)}_q\not\preccurlyeq_{\mathrm{imm}}B^{(r)}_{qm}$
-- statement:
--   Let $r\ge2$ and let $q,m$ be positive integers with
--   $$q\equiv1\pmod r,\qquad q>4r^2-2r,\qquad\gcd(m,r)=1,\qquad m\not\equiv\pm1\pmod r.$$
--   Then
--   $$D^{(r)}_q\not\preccurlyeq_{\mathrm m}D^{(r)}_{qm},\qquad B^{(r)}_q\not\preccurlyeq_{\mathrm m}B^{(r)}_{qm},\qquad B^{(r)}_q\not\preccurlyeq_{\mathrm{imm}}B^{(r)}_{qm}.$$
--
--   For $r\le4$ no $m$ satisfies the hypotheses (every unit modulo $r$ is $\pm1$); for $r=5$, $q=91$, $m=2$ they hold. This exclusion theorem places $D^{(r)}_{qp}$ and $B^{(r)}_{qp}$ in the forbidden classes of Theorem 11.
--
--   Differences from the source:
--   - encoding: congruences modulo $r$ → equalities of casts in `ZMod r`; reason: same instances
--   - encoding: $q>4r^2-2r$ → $4r^2<q+2r$ in $\mathbb N$; reason: avoids natural-number subtraction; same instances
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Theorem 9, p.9 (PDF p.11), conditions (4)

import Mathlib
import Definitions.Def_HadwigerConj_Defs
import Definitions.Def_RobersonCx_IsImmersion
import Definitions.Def_RobersonCx_circulantD

set_option autoImplicit false

namespace RobersonCx

/-- Theorem 9 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §4.1, p.9 (PDF p.11)). Let `r ≥ 2`, and let `q, m` be positive integers satisfying
`q ≡ 1 (mod r)`, `q > 4r² − 2r`, `gcd(m, r) = 1`, `m ≢ ±1 (mod r)` (4). Then `D^(r)_q ⋠_m D^(r)_{qm}`,
`B^(r)_q ⋠_m B^(r)_{qm}`, `B^(r)_q ⋠_imm B^(r)_{qm}`.

**Formalization Note** Congruences mod `r` are equalities in `ZMod r`; `q > 4r² − 2r` is `4r² < q + 2r`. For
`r ≤ 4` no `m` satisfies (4) (every unit mod `r` is `±1`); this is the paper's statement. -/
theorem theorem_9 (r q m : ℕ) (hr : 2 ≤ r) (hq0 : 0 < q) (hm0 : 0 < m) (hq1 : (q : ZMod r) = 1)
    (hq : 4 * r ^ 2 < q + 2 * r) (hmr : Nat.Coprime m r) (hm1 : (m : ZMod r) ≠ 1)
    (hm2 : (m : ZMod r) ≠ -1) :
    ¬ HadwigerConj.IsMinor (circulantD q r) (circulantD (q * m) r) ∧
    ¬ HadwigerConj.IsMinor (splitB q r) (splitB (q * m) r) ∧
    ¬ IsImmersion (splitB q r) (splitB (q * m) r) := by sorry

end RobersonCx
