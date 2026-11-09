-- Prove2me | Theorems.Thm_RecruitSmaller_lemma_3_9
-- name    : RecruitSmaller.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:55.684235+00:00
-- url     : https://prove2.me/theorems/b8e81c70-dc82-4b19-8661-dd33c0bd1b9b
-- title:
--   Lemma 3.9 — $\int_0^r\psi_{n,i}(w;p)f_{i,m}(w)\,dw\ge0$ for $m\ge n$
-- statement:
--   Let $m\ge n\ge i\ge1$ and $p\in[0,1]$, with $\psi_{n,i}$ the truncated integrand (3.10) and $f_{i,m}$ the Beta$(i,m-i+1)$ density. Then for every $r\in[0,1]$,
--   $$
--   \int_0^r\psi_{n,i}(w;p)\,f_{i,m}(w)\,dw\ \ge\ 0. \tag{3.13}
--   $$
--   Having more buyers ($m\ge n$) shifts Beta mass toward small $w$, where $\psi_{n,i}$ is larger, so the balanced-case inequality of Lemma 3.7 persists.
--
--   Differences from the source: none.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.9, p.15, eq. (3.13); proof pp.27–28

import Mathlib
import Definitions.Def_RecruitSmaller_psi
import Definitions.Def_RecruitSmaller_betaDens

namespace RecruitSmaller

/-- **Lemma 3.9** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.15, eq. (3.13); proof pp.27–28): let `m ≥ n ≥ i ≥ 1` and
`p ∈ [0, 1]`. Then for every `r ∈ [0, 1]`, `∫₀ʳ ψ_{n,i}(w; p) f_{i,m}(w) dw ≥ 0`. -/
theorem lemma_3_9 (m n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (hnm : n ≤ m)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ ∫ w in (0 : ℝ)..r, psi n i p w * betaDens m i w := by sorry

end RecruitSmaller
