-- Prove2me | Theorems.Thm_SilverRateLB_eq_19_fixed_eta
-- name    : SilverRateLB.eq_19_fixed_eta
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:34.682798+00:00
-- url     : https://prove2.me/theorems/60a53ec4-44bd-496d-a65e-5c01b7569559
-- title:
--   (19) — $\mathscr R_n(H)\ge n^{-p}/(2^{2p+1}a)$ for fixed $\eta$
-- statement:
--   Fix $0<\eta\le1/10$ and choose
--   $$p:=p_{\mathrm{sil}}+\eta,\qquad \gamma:=\frac\eta4,\qquad \varepsilon:=\Bigl(\frac\eta{16}\Bigr)^p,\qquad c:=\sqrt{1+2\gamma+\varepsilon^2},\tag{18}$$
--   with $a$ the constant of Lemma 2.4 for these $\varepsilon,\gamma$. Then for every $n\ge1$ and every $H\in[0,\infty)^n$,
--   $$\mathscr R_n(H)\ \ge\ \frac{1}{2^{2p+1}a}\,n^{-p}.\tag{19}$$
--
--   Combined with the growth estimate (20) for $a$ and the choice $\eta=\sqrt{\log\log n/\log n}$, this gives Theorem 1.1.
--
--   Differences from the source:
--   - encoding: ℛ_n with the paper's convention L = 1 (footnote 6, p. 6) → worstCaseRate 1; reason: the paper works with L = 1 in Sections 2–3 and the proofs; footnote 6 reduces every L to it
--   - encoding: H = (h_1, …, h_n) ∈ [0,∞)^n → H : List ℝ with nonnegative entries, n = H.length; reason: same schedules
--   - encoding: every n (implicit) → n ≥ 1; reason: at n = 0 the right-hand side n^{−p} is not defined (Lean returns 0) and the proof's Λ = a n^p ≥ a needs n ≥ 1
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), proof of Theorem 1.1, (18), (19), p. 15

import Mathlib
import Definitions.Def_SilverRateLB_pSil
import Definitions.Def_SilverRateLB_aOf
import Definitions.Def_SilverRateLB_worstCaseRate

namespace SilverRateLB

/-- **(19): the lower bound at a fixed `η`.** Fix `0 < η ≤ 1/10` and choose `p := p_sil + η`,
`γ := η/4`, `ε := (η/16)^p`, `c := √(1+2γ+ε²)` (18), with `a` as in Lemma 2.4. Then
`ℛ_n(H) ≥ (1/(2^{2p+1} a)) n^{−p}` for every `H ∈ [0,∞)^n`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, proof of Theorem 1.1, (18), (19), p. 15.

**Formalization Note** `ℛ_n` is `worstCaseRate 1` (footnote 6). `c` enters through `aOf ε γ`,
which uses `cOf ε γ = √(1+2γ+ε²)`. `n ≥ 1`: at `n = 0` Lean's `0^{−p} = 0` makes the bound
empty, and the proof's `Λ = a n^p ≥ a` needs `n ≥ 1`. -/
theorem eq_19_fixed_eta (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 10) (n : ℕ) (hn : 1 ≤ n)
    (H : List ℝ) (hlen : H.length = n) (hH : ∀ h ∈ H, 0 ≤ h) :
    ENNReal.ofReal (1 / (2 ^ (2 * (pSil + η) + 1) * aOf ((η / 16) ^ (pSil + η)) (η / 4)) *
        (n : ℝ) ^ (-(pSil + η))) ≤ worstCaseRate 1 H := by sorry

end SilverRateLB
