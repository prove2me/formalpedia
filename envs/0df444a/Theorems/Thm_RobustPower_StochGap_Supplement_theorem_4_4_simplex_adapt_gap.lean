-- Prove2me | Theorems.Thm_RobustPower_StochGap_Supplement_theorem_4_4_simplex_adapt_gap
-- name    : RobustPower.StochGap.Supplement.theorem_4_4_simplex_adapt_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T19:34:46.428245+00:00
-- url     : https://prove2.me/theorems/7b6a9c63-7c76-4b12-ab17-15b5f2b2e5e4
-- title:
--   Theorem 4.4, p. 26 — the adaptability gap is at least n for the corner simplex
-- statement:
--   Let $n\ge3$ and consider the instance with no first stage ($n_1=0$, $A=0$, $c=0$), $n_2=n$, no integer variables ($p_2=0$), $d=(1,\dots,1)$ and $B=I_n$ (so $m=n$), with the non-symmetric uncertainty set
--   $$I_b(\Omega)=\Bigl\{b\ \Big|\ \sum_{j=1}^{n} b_j\le1,\ b\ge0\Bigr\}\qquad(4.5).$$
--   Then
--   $$z_{\mathrm{Rob}}(b)\ \ge\ n\cdot z_{\mathrm{Adapt}}(b).$$
--
--   Without symmetry, the robust solution can therefore be worse than the optimal adaptive one by a factor growing with the dimension.
--
--   **Formalization Note** The range of $b$ is the published `SimplexGap.cornerSimplex n`. The adaptive value is `AdaptGap.zAdapt` with the constant all-ones cost; optimal values are EReal infima, and $n\cdot z$ is the product in EReal.
--
--   Differences from the source:
--
--   - encoding: optimal values defined by min over feasible solutions → EReal infima over the feasible set (⊤ when infeasible), no optimal solution assumed; reason: the published model of the base mission; the infimum equals the minimum whenever one is attained
--   - encoding: z_Adapt(b) of (1.3) and z_Rob(b) of (1.2) → AdaptGap.zAdapt with the constant cost d(ω) = d, and StochGap.zRob, where max_ω dᵀy is written dᵀy; reason: the two agree because the uncertainty set here is nonempty, so the maximum of a constant is that constant
--   - reading: the sum in (4.5) runs over j = 1, …, m → the sum runs over the n coordinates; reason: B = Iₙ ∈ ℝ^{m×n₂} with n₂ = n forces m = n, and the proof on p. 27 sums over n coordinates
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 26–27, Theorem 4.4 and (4.5)

import Mathlib
import Definitions.Def_RobustPower_StochGap_Problems
import Definitions.Def_RobustPower_AdaptGap_Problems
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

open Matrix

namespace RobustPower.StochGap.Supplement

/-- Theorem 4.4 (p. 26): for `n ≥ 3`, the instance with `n₁ = 0`, `n₂ = m = n`, no integer
variables, `A = 0`, `c = 0`, `d = (1, …, 1)`, `B = Iₙ` and uncertainty set the corner simplex
`{b | ∑ⱼ bⱼ ≤ 1, b ≥ 0}` (4.5) has `z_Rob(b) ≥ n · z_Adapt(b)`. -/
theorem theorem_4_4_simplex_adapt_gap {n : ℕ} (hn : 3 ≤ n) {Ω : Type*}
    (b : Ω → Fin n → ℝ)
    (hrange : Set.range b = RobustPower.SimplexGap.cornerSimplex n) :
    ((n : ℝ) : EReal) * RobustPower.AdaptGap.zAdapt (0 : Matrix (Fin n) (Fin 0) ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ) b 0 (fun _ _ => 1) ∅ ∅ ≤
      RobustPower.StochGap.zRob (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ)
        b ∅ ∅ 0 (fun _ => 1) := by sorry

end RobustPower.StochGap.Supplement
