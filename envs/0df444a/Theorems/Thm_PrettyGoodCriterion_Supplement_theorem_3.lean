-- Prove2me | Theorems.Thm_PrettyGoodCriterion_Supplement_theorem_3
-- name    : PrettyGoodCriterion.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:33:10.583546+00:00
-- url     : https://prove2.me/theorems/5b12c490-7e98-4e17-8882-55dd7fcd7601
-- title:
--   Theorem 3 — 2MQC improvement over the second MRRW bound: $R_2(\delta)\le R_{\mathrm{2MQC}}(\delta)<R^{(2)}_{\mathrm{MRRW}}(\delta)$
-- statement:
--   Let $h$ be the base-2 binary entropy, $s(D)=h\big((1-\sqrt{1-D})/2\big)$, and let $R_2(\delta)$ be the asymptotic rate function of binary codes. For $\delta\in(0,\tfrac12)$ let
--   $$
--   R^{(2)}_{\mathrm{MRRW}}(\delta):=\min_{0\le u\le1-2\delta}\Big[1+s(u^2)-s\big(u^2+2\delta u+2\delta\big)\Big]
--   $$
--   be the second MRRW bound (31), and let
--   $$
--   R_{\mathrm{2MQC}}(\delta):=\inf_{\substack{0\le v\le u\le1\\ v^2(u^2-v^2)<2\delta u^2(1-v^2)}}\Big[1+s(u^2)-s\big(A_\delta(u,v)\big)-s(v^2)\Big],\qquad A_\delta(u,v):=\min\left\{1,\frac{(u^2-v^2)^2+2\delta u^2(1+u)}{u^2(1-v^2)+v^2(u+v^2)}\right\},
--   $$
--   be the variational bound (46). Then for every $\delta\in(0,\tfrac12)$,
--   $$
--   R_2(\delta)\ \le\ R_{\mathrm{2MQC}}(\delta)\ <\ R^{(2)}_{\mathrm{MRRW}}(\delta).
--   $$
--
--   The first inequality comes from applying the pretty good criterion (Theorem 1) to the masked mixed-qubit channels. The second says that this family strictly improves the second MRRW bound, which had been the best known upper bound on $R_2$ for small relative distance, at every $\delta\in(0,\tfrac12)$.
--
--   **Formalization Note** $R_2$ is the base mission's published `PrettyGoodCriterion.rateFunction`. $R_{\mathrm{2MQC}}$ is the published `HoneycombCodes.R2MQC`, the real infimum of (46) over its strict feasible set; that definition gives $\lambda_\delta$ the value $2\delta$ at $(u,v)=(0,0)$, a point that is never feasible (checked in Lean), so the value is exactly (46). $R^{(2)}_{\mathrm{MRRW}}$ is the published `HoneycombCodes.M2`, the minimum (31) as a real `sInf` (attained); `g` there is $s$.
--
--   Differences from the source:
--   - encoding: $\min_{0\le u\le1-2\delta}$ in (31) → real `sInf` of the image of $[0,1-2\delta]$ (`HoneycombCodes.M2`); reason: the objective is continuous on the compact nonempty interval, so the infimum is attained and equals the minimum.
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Theorem 3, pp.4–5 (PDF 6–7); definitions (31), p.29 (PDF 31) and (46), p.35 (PDF 37); proof p.41 (PDF 43) via Corollary 24 and Proposition 26

import Mathlib
import Definitions.Def_PrettyGoodCriterion_rateFunction
import Definitions.Def_HoneycombCodes_R2MQC
import Definitions.Def_HoneycombCodes_M2

set_option autoImplicit false

namespace PrettyGoodCriterion.Supplement

/-- **Theorem 3 (2MQC improvement over the second MRRW bound)**, Alrabiah–Guruswami, *Binary code
rate bounds via classical–quantum channels*, arXiv:2608.09347 (held version), pp.4–5 (PDF 6–7);
proof p.41 (PDF 43) via Corollary 24 and Proposition 26.

For every `δ ∈ (0, 1/2)`, `R₂(δ) ⩽ R_2MQC(δ) < R^(2)_MRRW(δ)`, where `R_2MQC(δ)` is the variational
bound (46) and `R^(2)_MRRW(δ)` the second MRRW bound (31).

**Formalization Note.** `R₂` is the base mission's `PrettyGoodCriterion.rateFunction` (equation (1)).
`R_2MQC` is the published `HoneycombCodes.R2MQC`: the real infimum of `1 + s(u²) − s(A_δ(u, v)) − s(v²)`
over `0 ⩽ v ⩽ u ⩽ 1`, `v²(u² − v²) < 2δu²(1 − v²)`, exactly (46) (its special value of `λ_δ` at
`(0, 0)` is never used, since `(0, 0)` is not feasible). `R^(2)_MRRW` is the published `HoneycombCodes.M2`,
`min_{0⩽u⩽1−2δ} [1 + s(u²) − s(u² + 2δu + 2δ)]` as an attained real `sInf`, exactly (31). Both
conclusions are stated, the second strict. -/
theorem theorem_3 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    PrettyGoodCriterion.rateFunction δ ≤ HoneycombCodes.R2MQC δ ∧
      HoneycombCodes.R2MQC δ < HoneycombCodes.M2 δ := by sorry

end PrettyGoodCriterion.Supplement
