-- Prove2me | Theorems.Thm_RecruitSmaller_lemma_3_7
-- name    : RecruitSmaller.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:40.041525+00:00
-- url     : https://prove2.me/theorems/d3e7c303-0e3e-43ab-9f6b-2a15ddc3852d
-- title:
--   Lemma 3.7 — $\int_0^r\psi_{n,i}(w;p)f_{i,n}(w)\,dw\ge0$
-- statement:
--   For any integers $n\ge i\ge1$ and any $p\in[0,1]$, let
--   $$
--   \psi_{n,i}(w;p)=A_{n,i}(p)-\binom{n+2}{i}\min(1-p,w)^{n+2-i} \tag{3.10}
--   $$
--   on $[0,1]$, and let $f_{i,n}(w)=n\binom{n-1}{i-1}w^{i-1}(1-w)^{n-i}$ be the Beta$(i,n-i+1)$ density. Then for every $r\in[0,1]$,
--   $$
--   \int_0^r\psi_{n,i}(w;p)\,f_{i,n}(w)\,dw\ \ge\ 0. \tag{3.11}
--   $$
--   This is the core cancellation between recruitment gain and trade-reduction loss, in the balanced case $m=n$.
--
--   Differences from the source: none.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.7, p.14, eqs. (3.10)–(3.11); proof pp.25–26

import Mathlib
import Definitions.Def_RecruitSmaller_psi
import Definitions.Def_RecruitSmaller_betaDens

namespace RecruitSmaller

/-- **Lemma 3.7** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.14, eqs. (3.10)–(3.11); proof pp.25–26): for any
integers `n ≥ i ≥ 1` and any `p ∈ [0, 1]`, with the truncated integrand
`ψ_{n,i}(w; p) = A_{n,i}(p) − C(n+2, i) min(1 − p, w)^{n+2−i}`, for every `r ∈ [0, 1]`,
`∫₀ʳ ψ_{n,i}(w; p) f_{i,n}(w) dw ≥ 0`, where `f_{i,n}` is the Beta(i, n − i + 1) density. -/
theorem lemma_3_7 (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ ∫ w in (0 : ℝ)..r, psi n i p w * betaDens n i w := by sorry

end RecruitSmaller
