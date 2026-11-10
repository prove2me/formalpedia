-- Prove2me | Theorems.Thm_RobersonCx_lemma_20
-- name    : RobersonCx.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:39.47189+00:00
-- url     : https://prove2.me/theorems/14d44258-83a3-4819-b9c8-834d8a132414
-- title:
--   Lemma 20 — counting inequalities $(d_r(N)+1)q\le(d_r(q)+1)N$ and $(b_r(N)+1)q\le(b_r(q)+1)N$ from minor models
-- statement:
--   Let $r\ge2$, $q>4r^2-2r$ and $N\ge q$, with $\gcd(q,r)=\gcd(N,r)=1$. Then
--   $$D^{(r)}_q\preccurlyeq_{\mathrm m}D^{(r)}_N\ \Longrightarrow\ (d_r(N)+1)\,q\le(d_r(q)+1)\,N,$$
--   $$B^{(r)}_q\preccurlyeq_{\mathrm m}B^{(r)}_N\ \Longrightarrow\ (b_r(N)+1)\,q\le(b_r(q)+1)\,N,$$
--   with $d_r$, $b_r$ as in (6).
--
--   Substituting the parameters of Theorem 9 violates both inequalities, which proves the minor exclusions.
--
--   Differences from the source:
--   - encoding: $q>4r^2-2r$ → $4r^2<q+2r$ in $\mathbb N$; reason: avoids natural-number subtraction; same instances
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Lemma 20, p.17 (PDF p.19), eqs. (7), (8)

import Mathlib
import Definitions.Def_HadwigerConj_Defs
import Definitions.Def_RobersonCx_circulantD
import Definitions.Def_RobersonCx_aInv

set_option autoImplicit false

namespace RobersonCx

/-- Lemma 20 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. B, p.17 (PDF p.19)). Let `r ≥ 2`, `q > 4r² − 2r`, and `N ≥ q`, with
`gcd(q, r) = gcd(N, r) = 1`. Then `D^(r)_q ≼_m D^(r)_N ⟹ (d_r(N) + 1) q ≤ (d_r(q) + 1) N` (7), and
`B^(r)_q ≼_m B^(r)_N ⟹ (b_r(N) + 1) q ≤ (b_r(q) + 1) N` (8).

**Formalization Note** `q > 4r² − 2r` is `4r² < q + 2r`. `≼_m` is `HadwigerConj.IsMinor` (Definition 12).
`d_r`, `b_r` are `dR`, `bR` of eq. (6); their arguments satisfy `n > 2r` and `gcd(n, r) = 1` here. -/
theorem lemma_20 (r q N : ℕ) (hr : 2 ≤ r) (hq : 4 * r ^ 2 < q + 2 * r) (hN : q ≤ N)
    (hqr : Nat.Coprime q r) (hNr : Nat.Coprime N r) :
    (HadwigerConj.IsMinor (circulantD q r) (circulantD N r) → (dR N r + 1) * q ≤ (dR q r + 1) * N) ∧
    (HadwigerConj.IsMinor (splitB q r) (splitB N r) → (bR N r + 1) * q ≤ (bR q r + 1) * N) := by sorry

end RobersonCx
