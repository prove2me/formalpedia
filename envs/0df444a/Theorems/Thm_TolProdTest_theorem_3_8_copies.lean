-- Prove2me | Theorems.Thm_TolProdTest_theorem_3_8_copies
-- name    : TolProdTest.theorem_3_8_copies
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:26:20.375239+00:00
-- url     : https://prove2.me/theorems/5d51c4cd-3fb9-4984-80c2-fe7c6c438ae1
-- title:
--   Theorem 3.8, proof — copy count: $kT\le\exp(O(\Delta^{-5}\log^2(e/\Delta)))\log(2/\delta)$
-- statement:
--   There is an absolute constant $C_1>0$ such that for all $1\ge a>b\ge0$ and $\delta\in(0,1/2)$, with $\Delta=a-b$ and $k$, $T$ the parameters (68), (70) of Protocol 3.1,
--
--   $$
--   kT\ \le\ \exp\Big(C_1\,\Delta^{-5}\log^2\frac e\Delta\Big)\log\frac2\delta .
--   $$
--
--   This is the sample-complexity bound $2^{\tilde O(\Delta^{-5})}\log(2/\delta)$ of Theorem 3.8 and Theorem 1.1, independent of $n$ and $d$.
--
--   Differences from the source:
--   - encoding: the parameters c, η, q, R, k, p_Y, p_N, T of (67)–(70) with ceilings → protoC, protoEta, protoQ, protoR, protoK, protoPY, protoPN, protoT with ⌈·⌉₊ (Nat.ceil) and the natural logarithm; reason: all ceiling arguments are positive under 1 ≥ a > b ≥ 0, δ ∈ (0,1/2); log is natural (p.8)
--   - reading: O(·) in (78) → one absolute constant C₁ > 0 chosen before a, b, δ; reason: the O-constant of (76)–(78) depends on nothing
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), proof of Theorem 3.8, eqs. (75)–(78), p.18

import Mathlib
import Definitions.Def_TolProdTest_protoT

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Proof of Theorem 3.8, copy count**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eqs. (75)–(78), p.18: "The exact copy count of this construction is
kT = k⌈min{2, 8a^k} log(4/δ)/[a^k − ((a + b)/2)^k]²⌉. (75) … kT ≤ exp(O(∆^{−5} log²(e/∆))) log(2/δ) =
2^{Õ(∆^{−5})} log(2/δ). (78)"

There is an absolute constant `C₁ > 0` such that for all `1 ≥ a > b ≥ 0` and `δ ∈ (0, 1/2)`, with `Δ = a − b` and
`k, T` from (68), (70), `kT ≤ exp(C₁ Δ^{−5} log²(e/Δ)) log(2/δ)`.

**Formalization Note** The `O(·)` in (78) is the absolute constant `C₁`, quantified before `a, b, δ`. -/
theorem theorem_3_8_copies :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ a b δ : ℝ, 0 ≤ b → b < a → a ≤ 1 → 0 < δ → δ < 1 / 2 →
      ((protoK a b * protoT a b δ : ℕ) : ℝ) ≤
        Real.exp (C₁ * (a - b) ^ (-5 : ℝ) * Real.log (Real.exp 1 / (a - b)) ^ 2) * Real.log (2 / δ) := by sorry

end TolProdTest
