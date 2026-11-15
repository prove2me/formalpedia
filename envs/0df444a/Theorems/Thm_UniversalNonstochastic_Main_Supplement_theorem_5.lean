-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_theorem_5
-- name    : UniversalNonstochastic.Main.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:28:46.641402+00:00
-- url     : https://prove2.me/theorems/f189ebd8-a99c-4f21-a5d2-a86bd279ed90
-- title:
--   Theorem 5 — $-\log\mathbf m(N_{\alpha,\beta})=\min(\alpha,\mu(\beta))\pm c\log(\alpha+2)$
-- statement:
--   Let $N_{\alpha,\beta}$ be the set of $(\alpha,\beta)$-nonstochastic objects (no finite $\Omega\ni\omega$ with $K(\Omega)\le\alpha$ and $K(\omega\mid\Omega)\ge\log|\Omega|-\beta$), and $\mu$ the inverse busy beaver function. There is a constant $c>0$ such that for all $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty)$,
--   $$\bigl|-\log\mathbf m(N_{\alpha,\beta})-\min(\alpha,\mu(\beta))\bigr|\le c\log(\alpha+2).$$
--
--   The theorem describes the dependence of $\mathbf m(N_{\alpha,\beta})$ on $\beta$ completely, up to logarithmic precision in $\alpha$: it is $2^{-\mu(\beta)\pm O(\log(\alpha+2))}$ for $\beta<\mathrm{BB}(\alpha)$ and $2^{-\alpha\pm O(\log(\alpha+2))}$ otherwise.
--
--   Differences from the source:
--   - encoding: |−log m(N) − min(α, µ(β))| ≤ c log(α + 2) → 2^(−min(α,µ(β)) − c log₂(α+2)) ≤ m(N) ≤ 2^(−min(α,µ(β)) + c log₂(α+2)), with min(α, µ(β)) converted by toNat; reason: equivalent for m(N) > 0, which the source's inequality forces (−log 0 = ∞); min(α, µ(β)) ≤ α is finite, so the conversion is exact
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Theorem 5, p.7 (PDF p.7); absolute-value bars checked on the page image

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Stochasticity
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities

namespace UniversalNonstochastic.Main.Supplement

/-- Theorem 5, p.7: there is `c > 0` such that for all `α ∈ ℕ₀` and `β ∈ [0, ∞)`,
`|-log₂ m(N_{α,β}) - min(α, µ(β))| ≤ c log₂(α + 2)`, written as the equivalent two-sided bound
`2^{-min(α,µ(β)) - c log₂(α+2)} ≤ m(N_{α,β}) ≤ 2^{-min(α,µ(β)) + c log₂(α+2)}`.
`min(α, µ(β)) ≤ α` is finite, so `toNat` is exact. -/
theorem theorem_5 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) :
    ∃ c : ℝ, 0 < c ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β →
      (2 : ℝ) ^ (-(((min (α : ℕ∞) (invBusyBeaver U β)).toNat : ℕ) : ℝ) -
          c * Real.logb 2 ((α : ℝ) + 2)) ≤ mass m (nonstochastic U α β) ∧
        mass m (nonstochastic U α β) ≤
          (2 : ℝ) ^ (-(((min (α : ℕ∞) (invBusyBeaver U β)).toNat : ℕ) : ℝ) +
            c * Real.logb 2 ((α : ℝ) + 2)) := by sorry

end UniversalNonstochastic.Main.Supplement
