-- Prove2me | Theorems.Thm_TargetGranularity_SdVsMd_proposition_1
-- name    : TargetGranularity.SdVsMd.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:50.103997+00:00
-- url     : https://prove2.me/theorems/a53a7ef0-de4e-40bc-bb74-e3c463fec208
-- title:
--   Proposition 1, p. 15 (PDF 16), case (1−p)²/2 < c_click < (1−p)/2 — unique non-trivial sd equilibrium [ᾱ*,1] with click set [ω̄*,1]
-- statement:
--   Let $0<p<1$, $c_{ad}>0$, and let the click cost satisfy $\frac{(1-p)^2}{2}<c_{click}<\frac{1-p}{2}$ and $c_{ad}<\overline{c_{ad}}(c_{click},p)=p(1-p)\left(1+\log\frac{1-p}{2c_{click}}\right)$. Then there are $\bar\alpha^*\in[0,1)$ and $\overline\omega^*\in(0,1)$ such that
--
--   1. $\Sigma^{*sd}=[\bar\alpha^*,1]$ is a non-trivial sd equilibrium;
--   2. its click set is $\Omega^{*sd}=[\overline\omega^*,1]$, a positive fraction of the targeted consumers;
--   3. every non-trivial sd equilibrium coincides with $[\bar\alpha^*,1]$ up to a null set.
--
--   This is the sd half of the comparison in Proposition 3, in the range of click costs that Proposition 3 uses.
--
--   **Formalization Note** The statement is restricted to the middle case of $\overline{c_{ad}}$, where the page's $\underline\omega^{*sd}=0$; there the weight $\omega=0$ does not click, so the click set is $[\overline\omega^*,1]$. The page's hypothesis $c_{ad}\le\overline{c_{ad}}$ is made strict: at equality the cutoff is $\bar\alpha^*=1$ and $\{1\}$ is a null set, not a non-trivial equilibrium. Uniqueness is up to null sets, since targeting sets that differ by a null set induce the same posterior and profit.
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), p. 15 (PDF 16), Proposition 1; proof, pp. 34–35 (PDF 35–36), c̄_ad (middle case)

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

namespace TargetGranularity.SdVsMd

/-- Proposition 1, p. 15, in the regime `(1−p)²/2 < c_click < (1−p)/2` (with `c_ad < c̄_ad`):
there is a non-trivial sd equilibrium `[ᾱ*, 1]` with `ᾱ* < 1`, whose click set is `[ω̄*, 1]` with
`0 < ω̄* < 1`, and every non-trivial sd equilibrium equals `[ᾱ*, 1]` up to a null set. -/
theorem proposition_1 (p cad cclick : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hcad : 0 < cad)
    (hcadbar : cad < cadBar cclick p) (hclo : (1 - p) ^ 2 / 2 < cclick)
    (hchi : cclick < (1 - p) / 2) :
    ∃ αbar ωhi : ℝ, 0 ≤ αbar ∧ αbar < 1 ∧ 0 < ωhi ∧ ωhi < 1 ∧
      IsSdEq p cad cclick (Set.Icc αbar 1) ∧
      sdClick p cclick (Set.Icc αbar 1) = Set.Icc ωhi 1 ∧
      ∀ S : Set ℝ, IsSdEq p cad cclick S → S =ᵐ[MeasureTheory.volume] Set.Icc αbar 1 := by sorry

end TargetGranularity.SdVsMd
