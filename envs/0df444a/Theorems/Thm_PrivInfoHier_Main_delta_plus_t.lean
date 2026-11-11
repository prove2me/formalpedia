-- Prove2me | Theorems.Thm_PrivInfoHier_Main_delta_plus_t
-- name    : PrivInfoHier.Main.delta_plus_t
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:14:52.952586+00:00
-- url     : https://prove2.me/theorems/83b645b1-52c1-4cd4-9997-e47c3495b301
-- title:
--   §B.1, display after (B.5) — $\delta^+_t = 1-(1-\theta)^{t-1}$ on the B.1 process
-- statement:
--   Let $\theta\in(0,1)$, $\varepsilon>0$, and consider the App. B.1 process. Because $M_1=m_s$, the first mechanism is always safe, and the transcript up to time $t$ reveals the database if and only if one of $E_1,\dots,E_{t-1}$ equals $u$. Consequently, for every request strategy, all databases $x\neq x'$ and every $t\ge1$,
--   $$\delta^+_t=1-(1-\theta)^{t-1}.$$
--
--   Differences from the source:
--   - generalization: $Y^t$ with fixed requests → the full transcript $(R^t,Y^t)$ under every request strategy; reason: with fixed requests $Y^t$ determines the transcript.
--   - generalization: a neighbouring pair $x\sim x'$ → any pair $x\ne x'$; reason: neighbourliness plays no role on this process.
--   - reading: "$L_i(x,x')=\infty$ for all $x\sim x'$" → the hypothesis $x\neq x'$; reason: the unsafe mechanism reveals the database, which separates $x$ from $x'$ only when they differ (for $x=x'$, $\delta^+_t=0$).
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 18 (PDF 20), App. B.1, display after Eq. (B.5)

import Mathlib
import Definitions.Def_PrivInfoHier_Main_Model
import Definitions.Def_PrivInfoHier_Main_Filter
import Definitions.Def_PrivInfoHier_Main_B1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PrivInfoHier.Main

/-- App. B.1, display after (B.5): on the B.1 process, for distinct databases `x ≠ x′`, every
request strategy and every `t ≥ 1`, `δ⁺_t = 1 − (1 − θ)^{t−1}`. -/
theorem delta_plus_t (𝒳 ℛ : Type) [MeasurableSpace ℛ] (θ : Set.Ioo (0 : ℝ) 1) (ε : ℝ)
    (hε : 0 < ε) (A : RequestStrategy ℛ (B1Out 𝒳)) (x x' : 𝒳) (hxx' : x ≠ x') (t : ℕ)
    (ht : 1 ≤ t) :
    deltaPlus (b1Process 𝒳 ℛ θ) A x x' ε t = ENNReal.ofReal (1 - (1 - θ.1) ^ (t - 1)) := by sorry

end PrivInfoHier.Main
