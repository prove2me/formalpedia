-- Prove2me | Theorems.Thm_UnderstandingML_nn1_error_bound
-- name    : UnderstandingML.nn1_error_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:56:27.903323+00:00
-- url     : https://prove2.me/theorems/28c38b3f-5cdc-4642-bc0d-40d11700a522
-- title:
--   Theorem 19.3: for c-Lipschitz η on [0,1]^d, the 1-NN rule has E_S[L_D(h_S)] ≤ 2 L_D(h⋆) + 4 c √d m^{−1/(d+1)}
-- statement:
--   **Theorem 19.3.** Let $X = [0,1]^d$, $Y = \{0,1\}$, and $D$ be a distribution over $X \times Y$ for which the conditional probability function, $\eta$, is a $c$-Lipschitz function. Let $h_S$ denote the result of applying the 1-NN rule to a sample $S \sim D^m$. Then
--   $$\mathbb{E}_{S \sim D^m}[L_D(h_S)] \le 2L_D(h^\star) + 4c\sqrt{d}\, m^{-\frac{1}{d+1}}.$$
--
--   Formally: $D = $ `condLaw DX η` with $\eta$ valued in $[0,1]$, $h^\star = \mathbb{1}[\eta > 1/2]$, $h$ any 1-NN rule (any tie-breaking), measurable in $(S, x)$, and $m \ge 1$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §19.2.1 p. 262, Theorem 19.3

import Definitions.Def_UnderstandingML_NearestNeighbor

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 19.3** (p. 262). Let `X = [0,1]^d`, `Y = {0,1}`, and `D` be a distribution over
`X × Y` for which the conditional probability function `η` is a `c`-Lipschitz function. Let
`h_S` denote the result of applying the 1-NN rule to a sample `S ∼ D^m`. Then
`E_{S ∼ D^m}[L_D(h_S)] ≤ 2 L_D(h⋆) + 4 c √d m^{−1/(d+1)}`.
Here `D = condLaw D_X η`, `h⋆ = 𝟙[η > 1/2]`, the rule is any 1-NN rule, measurable in
`(S, x)`, and `m ≥ 1`. -/
theorem nn1_error_bound (d : ℕ) (DX : Measure (cube d)) [IsProbabilityMeasure DX]
    (η : cube d → ℝ) (c : NNReal) (hη : LipschitzWith c η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (h : Learner (cube d × Bool) (cube d → Bool)) (hnn : IsNN1Rule h)
    (hmeas : ∀ m, Measurable (fun p : (Fin m → cube d × Bool) × cube d ↦ h m p.1 p.2))
    (m : ℕ) (hm : 0 < m) :
    ∫ S, risk loss01 (condLaw DX η) (h m S) ∂(iidLaw (condLaw DX η) m) ≤
      2 * risk loss01 (condLaw DX η) (bayesRule η) +
        4 * c * Real.sqrt d * (m : ℝ) ^ (-(1 : ℝ) / (d + 1)) := by sorry

end UnderstandingML
