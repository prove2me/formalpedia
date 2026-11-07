-- Prove2me | Theorems.Thm_SamplingAC0_theorem_1
-- name    : SamplingAC0.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:56.585798+00:00
-- url     : https://prove2.me/theorems/4c4582c0-76e7-474f-98a1-6b7b762a5c9b
-- title:
--   Theorem 1 — direct product for sampling
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $b,d\ge1$ and $k\ge0$ be integers, $\epsilon>0$, and $D$ a distribution on $\{0,1\}^b$. Suppose a depth-$d$ forest $F$ with $kb$ output bits, on any number of input bits, has
--
--   $$\Delta\bigl(F(U),D^{\otimes k}\bigr)\le1-2\cdot2^{-c\epsilon^3k/(bd)} .$$
--
--   Then there is a depth-$d$ forest $F'$ with $b$ output bits (on some number of input bits) such that
--
--   $$\Delta\bigl(F'(U),D\bigr)\le\epsilon .$$
--
--   Sampling $k$ independent copies of $D$ even with tiny overlap forces sampling one copy well. The theorem reduces Theorem 4 to the inverse-polynomial bound of Theorem 10.
--
--   **Formalization Note** The output of $F$ is read as $k$ blocks of $b$ bits. Depth is the worst-case number of queries of each tree.
--
--   Differences from the source:
--   - encoding: depth-d forest, ϵ, D on {0,1}^b (b, d implicitly ≥ 1) → hypotheses 0 < b, 0 < d, 0 < ϵ; reason: the exponent cϵ³k/bd is undefined when bd = 0, and for ϵ ≤ 0 the hypothesis is unsatisfiable, so no instance is excluded
--   - encoding: c-notation (p.2); forests {0,1}^m → {0,1}^{kb} → one c > 0 before all objects; input lengths s, s' arbitrary; outputs indexed by Fin k × Fin b; reason: same instances
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 1, p.2 (proof pp.6–7)

import Mathlib
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SamplingAC0_tensorPow
set_option autoImplicit false

namespace SamplingAC0

/-- **Theorem 1 (direct product for sampling).** Riazanov–Viola, *Sampling Tools and the Power of
AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 1, p.2 (proof pp.6–7): "Let D be a
distribution on {0, 1}^b. Suppose a depth-d forest F has ∆(F(U), D^{⊗k}) ≤ 1 − 2 · 2^{−cϵ³k/bd},
then there is a depth-d forest F′ such that ∆(F′(U), D) ≤ ϵ."

The forest `F` has `k·b` output bits, read as `k` blocks of `b` bits, and any input length `s`;
`F′` has `b` output bits and any input length `s'`.

**Formalization Note.** The absolute constant `c` comes before all objects. `b ≥ 1` and `d ≥ 1`
are assumed because the exponent `cϵ³k/bd` is undefined otherwise. -/
theorem theorem_1 : ∃ c : ℝ, 0 < c ∧ ∀ (b d k : ℕ), 0 < b → 0 < d → ∀ ε : ℝ, 0 < ε →
    ∀ (D : PMF (Fin b → Bool)) (s : ℕ) (F : Forest s (Fin k × Fin b)), F.DepthLE d →
    tvDist (law (fun x : Fin s → Bool => fun (i : Fin k) (j : Fin b) => F.eval x (i, j)))
        (tensorPow D k) ≤ 1 - 2 * (2 : ℝ) ^ (-(c * ε ^ 3 * k / (b * d))) →
    ∃ (s' : ℕ) (F' : Forest s' (Fin b)), F'.DepthLE d ∧ tvDist (law F'.eval) D ≤ ε := by sorry

end SamplingAC0
