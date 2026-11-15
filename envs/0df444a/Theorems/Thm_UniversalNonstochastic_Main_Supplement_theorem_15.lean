-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_theorem_15
-- name    : UniversalNonstochastic.Main.Supplement.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:35:56.672652+00:00
-- url     : https://prove2.me/theorems/7a4c3385-5f59-43d1-bf7a-db9451dbab0f
-- title:
--   Theorem 15 — Theorems 13 and 14 above a complexity level $k$
-- statement:
--   Let $F$ and $d_p$ be as in Theorem 13. There is $c>0$ such that for all $\alpha,k\in\mathbb N_0$ and $\beta\in[0,\infty)$, each of the bounds in Theorems 13 and 14, of the form $\mathbf m(N)\ge L/c$ or $\mathbf m(N)\le cU$, remains true when $\mathbf m(N)$ is replaced by $\mathbf m(N\cap B)$, where $B$ is either $\{\omega\mid K(\omega)>k\}$ or $\{\omega\mid C(\omega)>k\}$, and $L$ and $U$ are replaced by $\min(L,\tau(k))$ and $\min(U,\tau(k))$:
--   $$\mathbf m(N\cap B)\ge\min(L,\tau(k))/c,\qquad \mathbf m(N\cap B)\le c\min(U,\tau(k)).$$
--
--   Spelled out, these are the eight lower and eight upper bounds of (18)–(25) and, for each $d\in\{d_e,d_p,d_K,d_F\}$, the lower bounds (26), (27) and the upper bound (28) for both measures; each for both choices of $B$, 64 inequalities in all, with one constant $c$ (also the $c$ inside $L$ and $U$). The theorem restates the frequency results as a constant share of the objects of high complexity.
--
--   Differences from the source:
--   - encoding: the meta-statement 'each of the bounds in Theorems 13 and 14' → the 32 bounds written out explicitly, for both B; reason: the expansion is literal; no bound is omitted
--   - encoding: d_p is one fixed largest randomness p-test → every d_p with IsLargestPTest d_p, quantified before the constant c; reason: the source fixes an arbitrary largest test; constants are chosen after it
--   - encoding: K(α) as a real exponent → ∃ κ : ℕ, K(α) = κ, and the bound with κ; reason: K(α) is valued in ℕ ∪ {∞} in Lean; for an optimal decoder it is finite, and asserting the witness avoids any default value of a conversion at ∞
--   - encoding: ∑ 2^(−F(ω)) = ∞ (resp. < ∞) → the ℝ≥0∞ sum ∑' (1/2)^F(ω) = ⊤ (resp. ≠ ⊤); reason: series of nonnegative terms; no real-tsum default
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Theorem 15, p.14 (PDF p.14)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Effective
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_ElementaryModels
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Deficiencies

open scoped ENNReal

namespace UniversalNonstochastic.Main.Supplement

/-- Theorem 15, p.14: let `F` and `d_p` be as in Theorem 13. There is `c > 0` such that for all
`α, k ∈ ℕ₀` and `β ∈ [0, ∞)`, each bound of Theorems 13 and 14 of the form `m(N) ≥ L/c` or
`m(N) ≤ c U` remains true when `m(N)` is replaced by `m(N ∩ B)`, with `B = {ω | K(ω) > k}` or
`B = {ω | C(ω) > k}`, and `L`, `U` replaced by `min(L, τ(k))`, `min(U, τ(k))`. Written out:
the 16 bounds of (18)–(25) and the 4 bounds (26), (27), (28) ×2 for each of the four `d`,
for both choices of `B` (64 inequalities); `κ = K(α)` is a natural number and the `c` inside
`L`, `U` is the same `c`. -/
theorem theorem_15 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) (V : OptimalPlainDecoder)
    (F : ℕ+ → ℕ) (hF : IsUpperSemicomputableNat F)
    (hdiv : ∑' ω : ℕ+, (2⁻¹ : ℝ≥0∞) ^ F ω = ⊤)
    (dp : ℕ+ → ElemMeasure → ℕ∞) (hdp : IsLargestPTest dp) :
    ∃ c : ℝ, 0 < c ∧ ∀ (α k : ℕ) (β : ℝ), 0 ≤ β →
      ∃ κ : ℕ, KNat U α = κ ∧
      ∀ B : Set ℕ+, (B = {ω | (k : ℕ∞) < Kobj U ω} ∨ B = {ω | (k : ℕ∞) < Cobj V ω}) →
        -- Theorem 13
        -- (18)
        (min ((2 : ℝ) ^ (-(α : ℝ))) (tail m (k : ℝ)) / c ≤ mass m (nonQuasiStochastic U (de U) α β ∩ B) ∧
          mass m (nonQuasiStochastic U (de U) α β ∩ B) ≤ c * min ((2 : ℝ) ^ (-(α : ℝ) + κ) + (2 : ℝ) ^ (-(2 : ℝ) ^ (β / 2 - c))) (tail m (k : ℝ))) ∧
        -- (19)
        (min ((2 : ℝ) ^ (-(α : ℝ))) (tail m (k : ℝ)) / c ≤ mass m (nonQuasiStochastic U (pDeficiency dp) α β ∩ B) ∧
          mass m (nonQuasiStochastic U (pDeficiency dp) α β ∩ B) ≤ c * min ((2 : ℝ) ^ (-(α : ℝ) + κ) + (2 : ℝ) ^ (-(2 : ℝ) ^ (β / 2 - c))) (tail m (k : ℝ))) ∧
        -- (20)
        (min ((2 : ℝ) ^ (-(α : ℝ))) (tail m (k : ℝ)) / c ≤ mass m (nonQuasiStochastic U (dK U) α β ∩ B) ∧
          mass m (nonQuasiStochastic U (dK U) α β ∩ B) ≤ c * min ((2 : ℝ) ^ (-(α : ℝ) + κ)) (tail m (k : ℝ))) ∧
        -- (21)
        (min ((2 : ℝ) ^ (-(α : ℝ)) + tail m (max (α : ℝ) β)) (tail m (k : ℝ)) / c ≤ mass m (nonQuasiStochastic U (dF F) α β ∩ B) ∧
          mass m (nonQuasiStochastic U (dF F) α β ∩ B) ≤ c * min ((2 : ℝ) ^ (-(α : ℝ) + κ) + tail m (max (α : ℝ) β)) (tail m (k : ℝ))) ∧
        -- (22)
        (min ((2 : ℝ) ^ (-(α : ℝ) - κ)) (tail m (k : ℝ)) / c ≤ mass m (nonQuasiStochasticC V (de U) α β ∩ B) ∧
          mass m (nonQuasiStochasticC V (de U) α β ∩ B) ≤ c * min ((2 : ℝ) ^ (-(α : ℝ)) + (2 : ℝ) ^ (-(2 : ℝ) ^ (β / 2 - c))) (tail m (k : ℝ))) ∧
        -- (23)
        (min ((2 : ℝ) ^ (-(α : ℝ) - κ)) (tail m (k : ℝ)) / c ≤ mass m (nonQuasiStochasticC V (pDeficiency dp) α β ∩ B) ∧
          mass m (nonQuasiStochasticC V (pDeficiency dp) α β ∩ B) ≤ c * min ((2 : ℝ) ^ (-(α : ℝ)) + (2 : ℝ) ^ (-(2 : ℝ) ^ (β / 2 - c))) (tail m (k : ℝ))) ∧
        -- (24)
        (min ((2 : ℝ) ^ (-(α : ℝ) - κ)) (tail m (k : ℝ)) / c ≤ mass m (nonQuasiStochasticC V (dK U) α β ∩ B) ∧
          mass m (nonQuasiStochasticC V (dK U) α β ∩ B) ≤ c * min ((2 : ℝ) ^ (-(α : ℝ))) (tail m (k : ℝ))) ∧
        -- (25)
        (min ((2 : ℝ) ^ (-(α : ℝ) - κ) + tail m (max (α : ℝ) β)) (tail m (k : ℝ)) / c ≤ mass m (nonQuasiStochasticC V (dF F) α β ∩ B) ∧
          mass m (nonQuasiStochasticC V (dF F) α β ∩ B) ≤ c * min ((2 : ℝ) ^ (-(α : ℝ)) + tail m (max (α : ℝ) β)) (tail m (k : ℝ))) ∧
        -- Theorem 14
        ∀ d : ℕ+ → ElemMeasure → EReal,
          (d = de U ∨ d = pDeficiency dp ∨ d = dK U ∨ d = dF F) →
          -- (26) lower bound
          min ((2 : ℝ) ^ (-(α : ℝ)) + tail m (max (α : ℝ) β)) (tail m (k : ℝ)) / c ≤ mass m (nonQuasiStochastic U (dset d) α β ∩ B) ∧
          -- (27) lower bound
          min ((2 : ℝ) ^ (-(α : ℝ) - κ) + tail m (max (α : ℝ) β)) (tail m (k : ℝ)) / c ≤ mass m (nonQuasiStochasticC V (dset d) α β ∩ B) ∧
          -- (28) upper bound for N_{α,β}(d^set)
          mass m (nonQuasiStochastic U (dset d) α β ∩ B) ≤ c * min ((2 : ℝ) ^ (-(α : ℝ) + c * Real.logb 2 ((α : ℝ) + 2)) + tail m (max (α : ℝ) β)) (tail m (k : ℝ)) ∧
          -- (28) upper bound for N^C_{α,β}(d^set)
          mass m (nonQuasiStochasticC V (dset d) α β ∩ B) ≤ c * min ((2 : ℝ) ^ (-(α : ℝ) + c * Real.logb 2 ((α : ℝ) + 2)) + tail m (max (α : ℝ) β)) (tail m (k : ℝ)) := by sorry

end UniversalNonstochastic.Main.Supplement
