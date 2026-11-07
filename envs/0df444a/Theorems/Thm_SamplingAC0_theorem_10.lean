-- Prove2me | Theorems.Thm_SamplingAC0_theorem_10
-- name    : SamplingAC0.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:47:42.339502+00:00
-- url     : https://prove2.me/theorems/cde9da8a-1ac0-4e85-8503-e1be7b01bc23
-- title:
--   Theorem 10 — one copy of $R$ is at distance $>q^{-3}$ from depth-$q^{1/10}$ forests
-- statement:
--   There is $Q$ such that for every $q=2^k\ge Q$ and every encoding of $\mathbb F_q$ by $k$ bits, every forest $f:\{0,1\}^s\to\{0,1\}^b$ of depth at most $q^{1/10}$, on any number $s$ of input bits, satisfies
--
--   $$\Delta\bigl(f(U),R\bigr)>q^{-3}.$$
--
--   This inverse-polynomial lower bound for a single copy of the point-line distribution, amplified by the direct-product Theorem 1, gives Theorem 4.
--
--   **Formalization Note** The threshold $Q$ is chosen before the encoding; the inequality is strict.
--
--   Differences from the source:
--   - generalization: R recorded with one unnamed encoding of points by 2k bits → every encoding enc, with Q chosen before enc; reason: the statement for every encoding specializes to the paper's
--   - encoding: "for a large enough q"; q a power of two; forests {0,1}^s → {0,1}^b → ∃ Q, q = 2^k ≥ Q; s arbitrary; outputs indexed by lines and point-list bits; depth a real bound on worst-case queries; reason: same instances
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 10, p.8 (proof §3.1–3.3, pp.9–12)

import Mathlib
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SamplingAC0_lineDNF
import Definitions.Def_SamplingAC0_R
set_option autoImplicit false

namespace SamplingAC0

/-- **Theorem 10 (one copy of `R` is far from shallow forests).** Riazanov–Viola, *Sampling Tools
and the Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 10, p.8 (proof
pp.9–12): "For a large enough q, every forest f : {0, 1}^s → {0, 1}^b of depth at most q^{1/10}
satisfies ∆(f(U), R) > q^{−3}."

**Formalization Note.** `q = 2^k`; the threshold `Q` comes before the encoding of field elements,
and the input length `s` is arbitrary. The inequality is strict. -/
theorem theorem_10 : ∃ Q : ℕ, ∀ (enc : Encoding) (k : ℕ), Q ≤ 2 ^ k →
    ∀ (s : ℕ) (f : Forest s (ROut k)), f.DepthLE (((2 : ℝ) ^ k) ^ ((1 : ℝ) / 10)) →
    tvDist (law f.eval) (R enc k) > ((2 : ℝ) ^ k) ^ (-3 : ℝ) := by sorry

end SamplingAC0
