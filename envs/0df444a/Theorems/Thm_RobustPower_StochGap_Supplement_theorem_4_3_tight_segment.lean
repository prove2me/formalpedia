-- Prove2me | Theorems.Thm_RobustPower_StochGap_Supplement_theorem_4_3_tight_segment
-- name    : RobustPower.StochGap.Supplement.theorem_4_3_tight_segment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:34:09.035825+00:00
-- url     : https://prove2.me/theorems/979cd3e2-e24a-401d-9365-d7bd0d6cb071
-- title:
--   Theorem 4.3, p. 25 (corrected: continuous recourse) — the adaptability gap 2 is attained on the segment b₁ + b₂ = 1
-- statement:
--   Consider the instance of §4.2: there is no first stage ($n_1=0$, $A=0$, $c=0$), $n_2=m=2$, $B=I_2$, $d=(1,1)$, the recourse is continuous ($p_2=0$), and the uncertainty set is the segment
--   $$I_b(\Omega)=\{b\in\mathbb R^2_+ : b_1+b_2=1\}.$$
--   Then
--   $$z_{\mathrm{Rob}}(b)=2\, z_{\mathrm{Adapt}}(b).$$
--
--   Here $z_{\mathrm{Rob}}(b)=2$ and $z_{\mathrm{Adapt}}(b)=1$, so the factor $2$ of Theorem 4.1 cannot be improved for symmetric uncertainty sets.
--
--   **Formalization Note** The range of $b:\Omega\to\mathbb R^2$ is exactly the segment. The adaptive value is `AdaptGap.zAdapt` with the constant cost $(1,1)$; optimal values are EReal infima.
--
--   Differences from the source:
--
--   - encoding: optimal values defined by min over feasible solutions → EReal infima over the feasible set (⊤ when infeasible), no optimal solution assumed; reason: the published model of the base mission; the infimum equals the minimum whenever one is attained
--   - encoding: z_Adapt(b) of (1.3) and z_Rob(b) of (1.2) → AdaptGap.zAdapt with the constant cost d(ω) = d, and StochGap.zRob, where max_ω dᵀy is written dᵀy; reason: the two agree because the uncertainty set here is nonempty, so the maximum of a constant is that constant
--   - correction: the instance leaves the number p₂ of integer recourse variables unspecified → no integer variables (I₂ = ∅); reason: the proof (p. 26) uses the continuous policy y(ω) = b(ω), and the equality is false for every p₂ > 0: with y₁ integer, a recourse covering (b₁, 1 − b₁), b₁ ∈ (0, 1], costs at least 2 − b₁, so z_Adapt = 2 = z_Rob (also when both coordinates are integer). Excluded: the instances with an integer recourse coordinate
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 25–26, instance of §4.2, Theorem 4.3 and its proof

import Mathlib
import Definitions.Def_RobustPower_StochGap_Problems
import Definitions.Def_RobustPower_AdaptGap_Problems

open Matrix

namespace RobustPower.StochGap.Supplement

/-- Theorem 4.3 (p. 25), with continuous recourse: the instance of §4.2 with `n₁ = 0`,
`n₂ = m = 2`, `A = 0`, `c = 0`, `d = (1, 1)`, `B = I₂`, no integer variables, and uncertainty
set `{b ∈ ℝ²₊ | b₁ + b₂ = 1}`. Then `z_Rob(b) = 2 · z_Adapt(b)`. -/
theorem theorem_4_3_tight_segment {Ω : Type*} (b : Ω → Fin 2 → ℝ)
    (hrange : Set.range b = {v : Fin 2 → ℝ | 0 ≤ v ∧ v 0 + v 1 = 1}) :
    RobustPower.StochGap.zRob (0 : Matrix (Fin 2) (Fin 0) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        b ∅ ∅ 0 (fun _ => 1) =
      2 * RobustPower.AdaptGap.zAdapt (0 : Matrix (Fin 2) (Fin 0) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) b 0 (fun _ _ => 1) ∅ ∅ := by sorry

end RobustPower.StochGap.Supplement
