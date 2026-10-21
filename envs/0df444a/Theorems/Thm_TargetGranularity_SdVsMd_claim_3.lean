-- Prove2me | Theorems.Thm_TargetGranularity_SdVsMd_claim_3
-- name    : TargetGranularity.SdVsMd.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:50.707738+00:00
-- url     : https://prove2.me/theorems/22558409-c3d3-47e0-aa34-9313801958e7
-- title:
--   Claim 3, p. 38 (PDF 39), first case — against Ω = [0,ω̲]∪[ω̄,1] with c_ad ≤ pω̲, c_ad ≤ p(1−ω̄), the md best response is Σmd(−c_ad/(p−c_ad), −(p−c_ad)/c_ad)
-- statement:
--   Let $0<p<1$ and $0<c_{ad}<p$, and let $\Omega=[0,\underline\omega]\cup[\overline\omega,1]$ with $0\le\underline\omega\le\overline\omega\le1$, $c_{ad}\le p\,\underline\omega$ and $c_{ad}\le p\,(1-\overline\omega)$. Then the consumers $(\alpha,\beta)\in[0,1]^2$ whose md ad value against $\Omega$ is non-negative,
--   $$\pi^{md}(\alpha,\beta;\Omega)=p\cdot|\{\omega\in\Omega:\omega\alpha+(1-\omega)\beta\ge p\}|-c_{ad}\ \ge 0,$$
--   form exactly the set $\Sigma^{md}(\gamma_1^*,\gamma_2^*)$ of Equation (6), with
--   $$\gamma_1^*=-\frac{c_{ad}}{p-c_{ad}},\qquad \gamma_2^*=-\frac{p-c_{ad}}{c_{ad}}.$$
--
--   This identifies the firm's best response in the md environment when both click intervals are long enough; note $\gamma_1^*\gamma_2^*=1$, so the best response is symmetric about the 45-degree line.
--
--   **Formalization Note** Only the first case of each of $\gamma_1^*$, $\gamma_2^*$ is formalized. The best response is read as the set of consumers with non-negative ad value (send an ad iff its value is $\ge 0$), and the equality is exact, including the boundary lines.
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), p. 38 (PDF 39), Claim 3 (first case of γ1* and γ2*), in the proof of Proposition 2

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

namespace TargetGranularity.SdVsMd

/-- Claim 3, p. 38, first case: against the click set `Ω = [0, ω̲] ∪ [ω̄, 1]` with
`c_ad ≤ p·ω̲` and `c_ad ≤ p·(1 − ω̄)`, the consumers of the unit square with non-negative md ad
value form exactly `Σ^md(γ₁*, γ₂*)` with `γ₁* = −c_ad/(p − c_ad)` and `γ₂* = −(p − c_ad)/c_ad`. -/
theorem claim_3 (p cad ωlo ωhi : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hcad : 0 < cad)
    (hcadp : cad < p) (hlo : 0 ≤ ωlo) (hlohi : ωlo ≤ ωhi) (hhi : ωhi ≤ 1)
    (hcadlo : cad ≤ p * ωlo) (hcadhi : cad ≤ p * (1 - ωhi)) :
    {x ∈ unitSq | 0 ≤ mdAdValue p cad (Set.Icc 0 ωlo ∪ Set.Icc ωhi 1) x} =
      mdSet p (-(cad / (p - cad))) (-((p - cad) / cad)) := by sorry

end TargetGranularity.SdVsMd
