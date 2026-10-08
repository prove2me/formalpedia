-- Prove2me | Theorems.Thm_SchmidliRuin_Exist_cond6_near_zero
-- name    : SchmidliRuin.Exist.cond6_near_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:45.791227+00:00
-- url     : https://prove2.me/theorems/bbb80e91-8f99-4d36-b394-26849e4d6111
-- title:
--   §4, pp. 898–899 — a local solution of (5) with Lemma 4's asymptotics satisfies (6) for small u ≠ 0
-- statement:
--   Assume the standing assumptions and that $G$ has a bounded density. Let $\varepsilon>0$, and let $g$ solve (5) on $[0,\varepsilon)$ with
--   $$
--   g(u)=\frac{\lambda}{c}-\alpha\sqrt u+o(\sqrt u)\quad(u\downarrow0),\qquad\alpha=\frac{\lambda\mu}{\sigma c^{3/2}} .
--   $$
--   Then there is $\varepsilon'\in(0,\varepsilon]$ such that condition (6) holds for every $u\in(0,\varepsilon')$:
--   $$
--   \inf_{b\in[0,1]}\lambda\Big(1-G(u/b)+\int_0^u\big(1-G((u-z)/b)\big)g(z)\,dz\Big)-\big(c-c(b)\big)g(u)>0 .
--   $$
--
--   Condition (6) is what lets a solution of (5) be continued. This statement establishes it near the origin, so that the maximal interval of existence in the proof of Theorem 2 is non-degenerate.
--
--   **Formalization Note.** The paper computes in the normalisation $\lambda=c=1$ of §4. The statement here keeps general $\lambda$ and $c$, as (6) is printed. $1-G(\cdot/b)$ at $b=0$ is read as $\mathbb P[0\cdot Y>\cdot]=0$. The integrand of (6) is $(1-G((u-z)/b))\,g(z)$; the page misplaces a parenthesis. $\varepsilon'\le\varepsilon$ is required because (6) at $u$ involves $g$ on $[0,u]$ only.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), pp. 898–899, §4, display (6) and the preceding computation

import Mathlib
import Definitions.Def_SchmidliRuin_Exist_Setting

namespace SchmidliRuin.Exist

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

/-- §4, pp. 898–899: a solution of (5) near `0` with the asymptotics of Lemma 4 satisfies
condition (6) for every small `u ≠ 0`. -/
theorem cond6_near_zero
    (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : SchmidliRuin.Verif.ReinsPremium c cb) (hν : SchmidliRuin.Verif.ClaimLaw ν)
    (hdens : HasBoundedDensity ν)
    (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℝ)
    (hg : SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g (Ico 0 ε))
    (hg_asymp : (fun u => g u - (lam / c - lam * mu / (sigma * c ^ ((3 : ℝ) / 2)) * Real.sqrt u))
        =o[𝓝[>] 0] (fun u => Real.sqrt u)) :
    ∃ ε' > 0, ε' ≤ ε ∧ ∀ u ∈ Ioo 0 ε', Cond6 c lam cb ν g u := by sorry

end SchmidliRuin.Exist
