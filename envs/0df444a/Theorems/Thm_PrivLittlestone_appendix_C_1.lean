-- Prove2me | Theorems.Thm_PrivLittlestone_appendix_C_1
-- name    : PrivLittlestone.appendix_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:35:33.829144+00:00
-- url     : https://prove2.me/theorems/adbc6924-c974-4ebd-ad64-aa91e7bb055c
-- title:
--   Appendix C.1 — with $c_{ph}=4096$, $c_{maj}=18$: $\Lambda > 3.7$, $\log m < 4\Lambda$, $a < 12\Lambda$ and the cap $20(L_0 + aq + 1) < K$
-- statement:
--   Fix $c_{\mathrm{ph}} = 4096$ and $c_{\mathrm{maj}} = 18$. Let $q \ge 1$ ($q = d$ for the oblivious construction, $q = r$ for flats), $T \ge 1$, $0 < \varepsilon \le 1$, $0 < \delta, \beta \le 1/2$,
--   $$
--   \Lambda = \log\frac{e(q+1)(T+1)}{\varepsilon\delta\beta}, \qquad K = \lceil 4096\, q \Lambda \rceil .
--   $$
--   Then $\Lambda \ge 1 + \log 16 > 3.7$, $K \le 8192(q+1)\Lambda$, $\log\Lambda \le \Lambda/e$,
--   $$
--   \log\frac{8K(T+1)}{\beta} \le \log 65536 + \Lambda - 1 + \log\Lambda < 5\Lambda,
--   $$
--   the oblivious sample size $m = \mathrm{oddceil}(18\log(8K(T+1)/\beta))$ satisfies $m \le 90\Lambda + 2 \le 91\Lambda$, $\log q \le \Lambda$, and the flats sample size $m = \lceil\log_2(8qK/\beta)\rceil$ satisfies $1 \le m \le 6\Lambda/\log 2 + 1 \le 9\Lambda$. For every sample size $1 \le m \le 91\Lambda$ (both applications), every $1 \le B \le 4(q+1)$ and every $L_0 \le \log 2 + q\log(2(q+1))$ (flats have $L_0 = 0$):
--   $$
--   \log m < 4\Lambda, \quad \eta < \tfrac14, \quad L_0 < 2q\Lambda,
--   $$
--   $$
--   a = \eta + \log\frac{128BKm(T+1)}{\delta} \le \tfrac14 + \log(512\cdot 8192) + 2\log(q+1) + \log\Lambda + \log m + \log(T+1) + \log(1/\delta) < 12\Lambda,
--   $$
--   $$
--   20(L_0 + aq + 1) < 20(14q\Lambda + 1) < 4096q\Lambda \le K .
--   $$
--
--   This verifies the cap condition (8) and the asymptotic estimates used in the main theorems.
--
--   **Formalization Note** $\eta$ and $a$ are (5)–(6) with this $K$, $m$, $B$; $\eta + \log(8B/\tau)$ with $\tau = \delta/(16Km(T+1))$ is the printed $\eta + \log(128BKm(T+1)/\delta)$.
--
--   Differences from the source:
--
--   - generalization: the two applications, with m ≤ 91Λ (oblivious) or m ≤ 9Λ (flats), B = 4(q+1) or B for flats, and L₀ ≤ log 2 + q log(2(q+1)) or L₀ = 0 → every m with 1 ≤ m ≤ 91Λ, every 1 ≤ B ≤ 4(q+1) and every L₀ ≤ log 2 + q log(2(q+1)); reason: both applications are instances; the paper's own estimates use only these bounds
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Appendix C.1, p.24

import Mathlib
import Definitions.Def_PrivLittlestone_bigLam
import Definitions.Def_PrivLittlestone_aP
import Definitions.Def_PrivLittlestone_oddceil

namespace PrivLittlestone

/-- **Appendix C.1, phase caps for the principal results** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Appendix C.1, p.24). With `c_ph = 4096`, `c_maj = 18`, `q ≥ 1` (`q = d` for the
oblivious construction, `q = r` for flats), `T ≥ 1`, `0 < ε ≤ 1`, `0 < δ, β ≤ 1/2`,
`Λ = log(e(q + 1)(T + 1)/(εδβ))` and `K = ⌈4096 qΛ⌉`:
`Λ ≥ 1 + log 16 > 3.7`, `K ≤ 8192(q + 1)Λ`, `log Λ ≤ Λ/e`,
`log(8K(T + 1)/β) ≤ log 65536 + Λ − 1 + log Λ < 5Λ`, the oblivious sample size
`m = oddceil(18 log(8K(T + 1)/β))` of (11) satisfies `m ≤ 90Λ + 2 ≤ 91Λ`; `log q ≤ Λ`, and the flats
sample size `m = ⌈log₂(8qK/β)⌉` satisfies `1 ≤ m ≤ 6Λ/log 2 + 1 ≤ 9Λ`; and for every sample size
`1 ≤ m ≤ 91Λ` (both applications), every `1 ≤ B ≤ 4(q + 1)` and every
`L₀ ≤ log 2 + q log(2(q + 1))` (the general construction; flats have `L₀ = 0`): `log m < 4Λ`,
`η < 1/4`, `a = η + log(128BKm(T + 1)/δ)
≤ 1/4 + log(512 · 8192) + 2 log(q + 1) + log Λ + log m + log(T + 1) + log(1/δ) < 12Λ`, `L₀ < 2qΛ`, and
`20(L₀ + aq + 1) < 20(14qΛ + 1) < 4096qΛ ≤ K`.

**Formalization Note** `η` and `a` are (5)–(6) with this `K, m, B`; `a = η + log(8B/τ)` with
`τ = δ/(16Km(T + 1))` is the printed `η + log(128BKm(T + 1)/δ)`. The flats sample size is an
instance of the universal clause, since `9Λ ≤ 91Λ`. `log₂` is `Real.logb 2`. -/
theorem appendix_C_1 (q T : ℕ) (ε δ β : ℝ) (hq : 1 ≤ q) (hT : 1 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hβ : 0 < β) (hβ1 : β ≤ 1 / 2) :
    1 + Real.log 16 ≤ bigLam q T ε δ β ∧ (37 / 10 : ℝ) < bigLam q T ε δ β ∧
      ((⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ : ℕ) : ℝ) ≤ 8192 * ((q : ℝ) + 1) * bigLam q T ε δ β ∧
      Real.log (bigLam q T ε δ β) ≤ bigLam q T ε δ β / Real.exp 1 ∧
      Real.log (8 * (⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ : ℝ) * ((T : ℝ) + 1) / β) ≤
        Real.log 65536 + bigLam q T ε δ β - 1 + Real.log (bigLam q T ε δ β) ∧
      Real.log (8 * (⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ : ℝ) * ((T : ℝ) + 1) / β) <
        5 * bigLam q T ε δ β ∧
      ((oddceil (18 * Real.log (8 * (⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ : ℝ) *
          ((T : ℝ) + 1) / β)) : ℕ) : ℝ) ≤ 90 * bigLam q T ε δ β + 2 ∧
      90 * bigLam q T ε δ β + 2 ≤ 91 * bigLam q T ε δ β ∧
      Real.log (q : ℝ) ≤ bigLam q T ε δ β ∧
      1 ≤ ⌈Real.logb 2 (8 * (q : ℝ) * (⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ : ℝ) / β)⌉₊ ∧
      ((⌈Real.logb 2 (8 * (q : ℝ) * (⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ : ℝ) / β)⌉₊ : ℕ) : ℝ) ≤
        6 * bigLam q T ε δ β / Real.log 2 + 1 ∧
      6 * bigLam q T ε δ β / Real.log 2 + 1 ≤ 9 * bigLam q T ε δ β ∧
      ∀ (m : ℕ) (B L0 : ℝ), 1 ≤ m → (m : ℝ) ≤ 91 * bigLam q T ε δ β → 1 ≤ B →
        B ≤ 4 * ((q : ℝ) + 1) → L0 ≤ Real.log 2 + (q : ℝ) * Real.log (2 * ((q : ℝ) + 1)) →
        Real.log (m : ℝ) < 4 * bigLam q T ε δ β ∧
        etaP ⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ m ε δ < 1 / 4 ∧
        aP ⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ m T B ε δ = etaP ⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ m ε δ +
          Real.log (128 * B * (⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ : ℝ) * (m : ℝ) * ((T : ℝ) + 1) / δ) ∧
        aP ⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ m T B ε δ ≤ 1 / 4 + Real.log (512 * 8192) + 2 * Real.log ((q : ℝ) + 1) +
          Real.log (bigLam q T ε δ β) + Real.log (m : ℝ) + Real.log ((T : ℝ) + 1) + Real.log (1 / δ) ∧
        aP ⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ m T B ε δ < 12 * bigLam q T ε δ β ∧
        L0 < 2 * (q : ℝ) * bigLam q T ε δ β ∧
        20 * (L0 + aP ⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ m T B ε δ * (q : ℝ) + 1) <
          ((⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ : ℕ) : ℝ) ∧
        20 * (L0 + aP ⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ m T B ε δ * (q : ℝ) + 1) <
          20 * (14 * (q : ℝ) * bigLam q T ε δ β + 1) ∧
        20 * (14 * (q : ℝ) * bigLam q T ε δ β + 1) < 4096 * (q : ℝ) * bigLam q T ε δ β ∧
        4096 * (q : ℝ) * bigLam q T ε δ β ≤ ((⌈4096 * (q : ℝ) * bigLam q T ε δ β⌉₊ : ℕ) : ℝ) := by sorry

end PrivLittlestone
