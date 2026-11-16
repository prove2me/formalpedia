-- Prove2me | Theorems.Thm_RobustBoolPCSP_Supplement_theorem_7_16
-- name    : RobustBoolPCSP.Supplement.theorem_7_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:39:52.826067+00:00
-- url     : https://prove2.me/theorems/1c203d49-35cc-4684-bbb5-707b7b07d684
-- title:
--   Theorem 7.16 (Finite product palette) — threshold codes with weak error $8\cdot3^J\epsilon+4e^{-2Nd^2}$
-- statement:
--   Fix a palette of §7.5 for $T^*$: $J$ four-query types with distributions $\lambda_j$, unary pin types, weights summing to one, and $\epsilon=\sum_jw_j\delta_j$. There are symmetric Boolean threshold functions $F_N(X)=\mathbf 1[t_N<\#\{i:X_i=1\}]$ and a constant $d>0$ such that:
--
--   1. $F_N(0^N)=0$ and $F_N(1^N)=1$ for $N\ge1$;
--   2. under every query product measure and the uniform measure, the influences of all coordinates tend to zero as $N\to\infty$;
--   3. for every $N$ and every choice of query coordinate permutations, the weak error is at most
--   $$8\cdot3^J\epsilon+4\exp(-2Nd^2).$$
--
--   Moreover, if $e$ bounds every $\delta_j$ and $(2\cdot3^J-1)e<1/4$, there are symmetric threshold functions whose weak error tends to zero.
--
--   Within this architecture a fixed finite family of tests cannot force more than a constant-factor cost, which explains why the balance tester needs $\Theta(\log(1/\eta))$ scales.
--
--   Differences from the source:
--   - reading: correct on 0^N and 1^N → for N ≥ 1; reason: for N = 0 the two strings coincide
--   - encoding: influences tending to zero → resampling influences, uniformly over the coordinates; reason: proportional to the variance-normalized influence of a Boolean function on each product measure
--   - encoding: o_N(1), and the remainder at most 4 exp(−2Nd²) → the bound 8·3^J ϵ + 4 exp(−2Nd²) for every N; reason: the theorem's second sentence makes the remainder explicit
--   - generalization: if every type individually satisfies δ_j ≤ ϵ → for every e with δ_j ≤ e for all types and (2·3^J − 1)e < 1/4; reason: specializes to e = ϵ; the proof uses only the bound on each δ_j
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), Theorem 7.16, pp.66–67

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_BoolOps
import Definitions.Def_RobustBoolPCSP_Supplement_ProductPalette

set_option autoImplicit false

open Filter Topology

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- **Theorem 7.16 (Finite product palette)**, pp.66–67. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"Within this architecture, there exist symmetric Boolean threshold functions F_N that are correct on
0^N and 1^N, have influences tending to zero under every query product measure and the uniform
measure, and incur weak error at most 8 · 3^J ϵ + o_N(1). (70) For each fixed palette, there is a
constant d > 0 such that the remainder is at most 4 exp(−2N d²). If every type individually
satisfies δ_j ≤ ϵ, the weak error can be made to tend to zero whenever (2 · 3^J − 1)ϵ < 1/4."

**Formalization Note.** The architecture of §7.5 is `Palette` (for `T∗`), `ϵ = Palette.eps`, the
weak error `paletteWeakErr` (for every choice of query coordinate permutations). A symmetric
threshold function is `F_N(X) = 1[t_N < #ones(X)]`. Correctness on `0^N`, `1^N` is asserted for
`N ≥ 1` (for `N = 0` the two strings coincide). Influences are resampling influences (`resampInf`)
under every query bias (`Palette.queryBias`) and `1/2`, and tend to zero uniformly over the
coordinates. The remainder bound `4 exp(−2Nd²)` makes `o_N(1)` explicit. In the last sentence `ϵ` is
any number bounding every `δ_j` (the palette's own `ϵ` is a special case), and the conclusion is
another family of symmetric threshold functions with weak error tending to zero. -/
theorem theorem_7_16 (pal : Palette) :
    (∃ (F : (N : ℕ) → (Fin N → Bool) → Bool) (d : ℝ), 0 < d ∧
      (∀ N : ℕ, ∃ t : ℝ, ∀ X : Fin N → Bool, F N X = decide (t < (onesCount X : ℝ))) ∧
      (∀ N : ℕ, 1 ≤ N → F N (fun _ => false) = false ∧ F N (fun _ => true) = true) ∧
      (∀ p : ℝ, (p ∈ pal.queryBias ∨ p = 1 / 2) → ∀ e : ℝ, 0 < e → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ i : Fin N, resampInf p (F N) i ≤ e) ∧
      (∀ (N : ℕ) (σ : Fin pal.J → Fin 4 → Equiv.Perm (Fin N)),
        paletteWeakErr pal N (F N) σ ≤
          8 * 3 ^ pal.J * pal.eps + 4 * Real.exp (-2 * N * d ^ 2))) ∧
    (∀ e : ℝ, (∀ j, pal.delta4 j ≤ e) → (∀ k, pal.deltaU k ≤ e) → (2 * 3 ^ pal.J - 1) * e < 1 / 4 →
      ∃ F : (N : ℕ) → (Fin N → Bool) → Bool,
        (∀ N : ℕ, ∃ t : ℝ, ∀ X : Fin N → Bool, F N X = decide (t < (onesCount X : ℝ))) ∧
        ∀ σ : (N : ℕ) → Fin pal.J → Fin 4 → Equiv.Perm (Fin N),
          Tendsto (fun N => paletteWeakErr pal N (F N) (σ N)) atTop (𝓝 0)) := by sorry

end RobustBoolPCSP.Supplement
