-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_theorem_9
-- name    : UniversalNonstochastic.Main.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:32:33.159218+00:00
-- url     : https://prove2.me/theorems/6f12d155-8d55-482e-bbc1-5cf25943437c
-- title:
--   Theorem 9 — $\mathbf m(N^Q_{\alpha,\beta})\ge2^{-\alpha-\mu(\beta)-c}$
-- statement:
--   Fix a Gödel numbering, and let $N^Q_{\alpha,\beta}$ be the set of objects that are not $(\alpha,\beta)$-Quasi-stochastic: no probability measure $P$ on $\mathcal X$ with a number $\pi$ has $K(\pi)\le\alpha$ and $K(\omega\mid\pi)\ge-\log P(\{\omega\})-\beta$. There is $c>0$ such that for all $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty)$,
--   $$\mathbf m(N^Q_{\alpha,\beta})\ge2^{-\alpha-\mu(\beta)-c}.$$
--
--   This is the analogue of the lower bound of Theorem 7 for general computable probability measures as models, which may have infinite support; the bound tends to $0$ as $\beta\to\infty$.
--
--   Differences from the source:
--   - encoding: a fixed Gödel numbering of the algorithms from X × N to rational numbers → an arbitrary GodelNumbering parameter (acceptable numbering with positive indices, rational-name outputs), quantified before the constants; reason: the source's Gödel numberings are acceptable numberings; the statement holds for every one
--   - reading: outputs a rational number within 2^(−n) of P({ω}) → |P({ω}) − q| ≤ 2^(−n); reason: 'within' can be read with ≤ or <; ≤ admits more numbers π, which is the stronger reading for this statement
--   - encoding: µ(β) as a real exponent → ∃ μ : ℕ, µ(β) = μ, and the bound with μ; reason: µ is an ℕ∞-valued infimum; it is attained and finite, and asserting the witness avoids any default value of a conversion at ∞
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Theorem 9, p.10 (PDF p.10); definitions on p.9

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities
import Definitions.Def_UniversalNonstochastic_Main_Supplement_ComputableModels

namespace UniversalNonstochastic.Main.Supplement

/-- Theorem 9, p.10: for the fixed Gödel numbering `G` there is `c > 0` such that for all
`α ∈ ℕ₀` and `β ∈ [0, ∞)`, `m(N^Q_{α,β}) ≥ 2^{-α-µ(β)-c}` (with `µ(β)` a natural number). -/
theorem theorem_9 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) (G : GodelNumbering) :
    ∃ c : ℝ, 0 < c ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β →
      ∃ μ : ℕ, invBusyBeaver U β = μ ∧
        (2 : ℝ) ^ (-(α : ℝ) - μ - c) ≤ mass m (nonQuasiStochasticGen G U α β) := by sorry

end UniversalNonstochastic.Main.Supplement
