-- Prove2me | Theorems.Thm_PrivInfoHier_Main_eq_B_2
-- name    : PrivInfoHier.Main.eq_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:14:40.990047+00:00
-- url     : https://prove2.me/theorems/cf8958ae-441d-4e95-b10d-1f2136de3026
-- title:
--   §B.1, Eq. (B.2) — the mechanism-level filter $T_M$ is geometric, with its quantile function
-- statement:
--   Let $\theta\in(0,1)$ and consider the App. B.1 process, with $T_M$ the filter that stops just before the first execution of the unsafe mechanism. Since $M_1=m_s$, the first instance of $m_u$ is distributed as $\mathrm{Geom}(\theta)+1$, so $T_M\sim\mathrm{Geom}(\theta)$ on $\{1,2,\dots\}$. For every database $x$ and every request strategy $\mathcal A$, under $P_{x,\mathcal A}$:
--   $$P(T_M=t+1)=(1-\theta)^t\theta,\qquad P(T_M\le t)=1-(1-\theta)^t\qquad(t\ge0),$$
--   and for $0\le u<1$
--   $$Q_{T_M}(u)=\Big\lceil\frac{\log(1-u)}{\log(1-\theta)}\Big\rceil\ \ge\ \frac{\log(1-u)}{\log(1-\theta)}.$$
--   This is the distributional input to the lower bound of Theorem 3.2.
--
--   Differences from the source:
--   - generalization: fixed requests (trivial request strategy) → every request space and every request strategy; reason: the B.1 rules ignore requests and App. B (p. 17) says the arguments hold uniformly over the strategy; the fixed-request case is a special case.
--   - reading: the quantile is dropped of its $x$-dependence (footnote 4) → the statement holds under every database $x$ and every strategy; reason: footnote 4 says the setup is symmetric in $x$.
--   - reading: "the quantile function" (convention not fixed) → $Q(u)=\inf\{t\in\mathbb N:P(T\le t)\ge u\}$ in $[0,\infty]$, for $u\in[0,1)$; reason: the left-continuous inverse is the convention that gives the printed ceiling formula.
--   - reading: "$T_M\sim\mathrm{Geom}(\theta)$" → $P(T_M=t+1)=(1-\theta)^t\theta$ for $t\ge0$; reason: the printed CDF $1-(1-\theta)^t$ fixes the support $\{1,2,\dots\}$.
--   - encoding: $T_M=+\infty$ on the null event that $m_u$ never runs → $T_M=0$ there (`sInf ∅`); reason: ℕ-valued; the event has probability $0$, so no probability changes.
--   - encoding: a filter on $\Omega=\mathcal Z\times(\mathcal R\times\mathcal Y)^{\mathbb N}$ under $\mathrm{law}(Z)\otimes P_{x,\mathcal A}$ → $T_M$ a function of the interaction path alone, its law under $P_{x,\mathcal A}$; reason: $T_M$ uses no internal randomness (a deterministic filter, p. 7), so its law is the same on either space.
--   - encoding: $\lceil\cdot\rceil$ → `Nat.ceil`, the probabilities as `ENNReal.ofReal` of the real values; reason: the argument is $\ge0$ for $u\in[0,1)$, so the integer ceiling and `Nat.ceil` agree.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 17 (PDF 19), App. B.1, Eq. (B.2)

import Mathlib
import Definitions.Def_PrivInfoHier_Main_Model
import Definitions.Def_PrivInfoHier_Main_Filter
import Definitions.Def_PrivInfoHier_Main_B1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PrivInfoHier.Main

/-- App. B.1, (B.2): on the B.1 process the filter `T_M` that stops just before the first `m_u`
is geometric: `P(T_M = t + 1) = (1 − θ)^t θ`, `P(T_M ≤ t) = 1 − (1 − θ)^t`, and its quantile
function is `Q(u) = ⌈log(1 − u)/log(1 − θ)⌉ ≥ log(1 − u)/log(1 − θ)` for `u ∈ [0, 1)`; for every
database and every request strategy. -/
theorem eq_B_2 (𝒳 ℛ : Type) [MeasurableSpace ℛ] (θ : Set.Ioo (0 : ℝ) 1)
    (A : RequestStrategy ℛ (B1Out 𝒳)) (x : 𝒳) :
    (∀ t : ℕ, interLaw (b1Process 𝒳 ℛ θ) A x {p | TM 𝒳 ℛ θ p = t + 1}
        = ENNReal.ofReal ((1 - θ.1) ^ t * θ.1)) ∧
    (∀ t : ℕ, interLaw (b1Process 𝒳 ℛ θ) A x {p | TM 𝒳 ℛ θ p ≤ t}
        = ENNReal.ofReal (1 - (1 - θ.1) ^ t)) ∧
    (∀ u : ℝ, 0 ≤ u → u < 1 →
      quantile (interLaw (b1Process 𝒳 ℛ θ) A x) (TM 𝒳 ℛ θ) u
          = ((⌈Real.log (1 - u) / Real.log (1 - θ.1)⌉₊ : ℕ) : ℝ≥0∞) ∧
        ENNReal.ofReal (Real.log (1 - u) / Real.log (1 - θ.1))
          ≤ quantile (interLaw (b1Process 𝒳 ℛ θ) A x) (TM 𝒳 ℛ θ) u) := by sorry

end PrivInfoHier.Main
