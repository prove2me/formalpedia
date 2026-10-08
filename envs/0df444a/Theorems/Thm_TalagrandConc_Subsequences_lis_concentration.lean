-- Prove2me | Theorems.Thm_TalagrandConc_Subsequences_lis_concentration
-- name    : TalagrandConc.Subsequences.lis_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:25.612155+00:00
-- url     : https://prove2.me/theorems/7a286268-6daf-4e73-940f-10b715dd78f0
-- title:
--   Theorem 7.1.2 — P(L_N ≥ M+u) ≤ 2exp(−u²/(4(M+u))) and P(L_N ≤ M−u) ≤ 2exp(−u²/(4M))
-- statement:
--   Let $X_1,\dots,X_N$ be independent random variables on $[0,1]$, uniformly distributed or, more generally, distributed according to a common non-atomic probability $\mu$. Let $L_N = L_N(X_1,\dots,X_N)$ be the length of the longest increasing subsequence of $X_1,\dots,X_N$ (the largest $p$ with $i_1 < \dots < i_p$ and $X_{i_1} \le \dots \le X_{i_p}$), and let $M = M_N$ be a median of $L_N$. Then for all $u > 0$,
--   $$P(L_N \ge M + u) \le 2\exp\Big(-\frac{u^2}{4(M+u)}\Big), \tag{7.1.3}$$
--   $$P(L_N \le M - u) \le 2\exp\Big(-\frac{u^2}{4M}\Big). \tag{7.1.4}$$
--
--   Since $L_N$ is distributed like the longest increasing subsequence of a uniform random permutation and $M_N$ grows like $2\sqrt N$, these bounds show that $L_N$ fluctuates around its median on the scale $N^{1/4}$, sharper than the scale $\sqrt N$ given by martingale methods.
--
--   **Formalization Note** The variables are the coordinates of $[0,1]^N$ under $P = \mu^{\otimes N}$, where $\mu$ is any probability measure on $[0,1]$ with $\mu(\{t\}) = 0$ for every $t$ (this includes Lebesgue measure). When $M = 0$ (only possible for $N = 0$) Lean's division gives $u^2/(4M) = 0$, so (7.1.4) reads $P(L_N \le -u) \le 2$; the event is empty, so nothing is lost.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 153, Theorem 7.1.2, Eqs. (7.1.3)–(7.1.4)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic
import Definitions.Def_TalagrandConc_Subsequences_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.Subsequences

/-- Talagrand (1995), Theorem 7.1.2, p. 153. Let `X_1, …, X_N` be i.i.d. on `[0,1]` with a
non-atomic law `μ` (e.g. uniform), realised as the coordinates of `[0,1]^N` under
`P = μ^{⊗N}`, and let `M` be a median of `L_N`. For all `u > 0`,
(7.1.3) `P(L_N ≥ M + u) ≤ 2 exp(−u² / (4(M + u)))` and
(7.1.4) `P(L_N ≤ M − u) ≤ 2 exp(−u² / (4M))`. -/
theorem lis_concentration {N : ℕ} (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (hμ : ∀ t : unitInterval, μ {t} = 0) (M : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian (Measure.pi fun _ : Fin N => μ) (fun x => (lis x : ℝ)) M)
    (u : ℝ) (hu : 0 < u) :
    (Measure.pi fun _ : Fin N => μ) {x | M + u ≤ (lis x : ℝ)} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (4 * (M + u))))) ∧
      (Measure.pi fun _ : Fin N => μ) {x | (lis x : ℝ) ≤ M - u} ≤
        ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / (4 * M)))) := by sorry

end TalagrandConc.Subsequences
