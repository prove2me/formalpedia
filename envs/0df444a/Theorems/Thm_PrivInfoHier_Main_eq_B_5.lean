-- Prove2me | Theorems.Thm_PrivInfoHier_Main_eq_B_5
-- name    : PrivInfoHier.Main.eq_B_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:14:48.135703+00:00
-- url     : https://prove2.me/theorems/cd142014-c138-4f8c-8f78-b8f5bcdd60eb
-- title:
--   §B.1, Eq. (B.5) — hockey-stick identity for $\delta^+_t$ on the B.1 process
-- statement:
--   Let $\theta\in(0,1)$, $\varepsilon>0$, and consider the App. B.1 process. For every request strategy, every pair of databases $x,x'$ and every $t\ge0$, the smallest $\delta$ for which the transcript after $t$ releases satisfies the $(\varepsilon,\delta)$-DP inequality from $x$ to $x'$ is given by the standard identity
--   $$\delta^+_t:=\sup_S\Big(P_x\big((R^t,Y^t)\in S\big)-e^\varepsilon P_{x'}\big((R^t,Y^t)\in S\big)\Big)=\mathbb E_x\Big[\big(1-e^{\varepsilon-L^{(t)}}\big)_+\Big],$$
--   the supremum over measurable sets of transcripts, where $e^{-L^{(t)}}=\prod_{i\le t}\frac{\mathrm dm_i(x')}{\mathrm dm_i(x)}(Y_i)$.
--
--   Differences from the source:
--   - generalization: $Y^t$ with fixed requests → the full transcript $(R^t,Y^t)$ under every request strategy; reason: with fixed requests $Y^t$ determines the transcript (p. 18), so the two suprema agree there.
--   - generalization: neighbouring $x\sim x'$ → every pair $x,x'$; reason: the identity holds for any two databases.
--   - reading: "the standard identity" used for the transcript of the B.1 process → stated for the B.1 process; reason: (B.5) is displayed inside App. B.1 for this process; a version for every process would need measurability assumptions on the density ratios that the paper does not state.
--   - encoding: $e^{\varepsilon-L^{(t)}}$ and $(\cdot)_+$ → `ofReal (exp ε) * expNegCumLoss` and truncated subtraction in $[0,\infty]$; reason: $e^{-L_i}$ is the density ratio, never undefined; $(1-a)_+$ is `1 - a` in `ℝ≥0∞`.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 18 (PDF 20), App. B.1, Eq. (B.5)

import Mathlib
import Definitions.Def_PrivInfoHier_Main_Model
import Definitions.Def_PrivInfoHier_Main_Filter
import Definitions.Def_PrivInfoHier_Main_B1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PrivInfoHier.Main

/-- App. B.1, (B.5): on the B.1 process, for every request strategy, every pair of databases and
every `t`, `δ⁺_t = sup_S (P_x((R^t, Y^t) ∈ S) − e^ε P_{x′}((R^t, Y^t) ∈ S)) = E_x[(1 − e^{ε − L^{(t)}})_+]`,
where `e^{−L^{(t)}}` is the product of the density ratios `dm_i(x′)/dm_i(x)` at the outputs. -/
theorem eq_B_5 (𝒳 ℛ : Type) [MeasurableSpace ℛ] (θ : Set.Ioo (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (A : RequestStrategy ℛ (B1Out 𝒳)) (x x' : 𝒳) (t : ℕ) :
    deltaPlus (b1Process 𝒳 ℛ θ) A x x' ε t
      = ∫⁻ p, (1 - ENNReal.ofReal (Real.exp ε) * expNegCumLoss (b1Process 𝒳 ℛ θ) x x' t p)
          ∂(interLaw (b1Process 𝒳 ℛ θ) A x) := by sorry

end PrivInfoHier.Main
