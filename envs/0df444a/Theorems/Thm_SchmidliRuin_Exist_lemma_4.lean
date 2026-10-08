-- Prove2me | Theorems.Thm_SchmidliRuin_Exist_lemma_4
-- name    : SchmidliRuin.Exist.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:22.873901+00:00
-- url     : https://prove2.me/theorems/65a66683-d08b-4330-867c-d6d1fe93dc55
-- title:
--   Lemma 4, p. 898 — local solution of (5) on [0, ε) with g(u) = λ/c − α√u + o(√u), α = λµ/(σc^{3/2})
-- statement:
--   Assume the standing assumptions, and suppose the claim-size distribution $G$ has a bounded density. Then there are $\varepsilon>0$ and a function $g$ solving equation (5) on $[0,\varepsilon)$. Here (5) is
--   $$
--   g(u)=\frac{1}{\dfrac{\mu^2}{2\sigma^2}\displaystyle\int_0^u\frac{dx}{\inf_{b\in[0,1]}\lambda\big(1-G(x/b)+\int_0^x(1-G((x-z)/b))g(z)\,dz\big)-(c-c(b))g(x)}+\dfrac{c}{\lambda}} .
--   $$
--   Moreover, as $u\downarrow0$,
--   $$
--   g(u)=\frac{\lambda}{c}-\alpha\sqrt u+o(\sqrt u),\qquad \alpha=\frac{\lambda\mu}{\sigma c^{3/2}} .
--   $$
--
--   This is the starting point of the existence proof. The solution exists near $0$, and its square-root behaviour is what later shows condition (6) for small $u$.
--
--   **Formalization Note.** "Solving (5) on $[0,\varepsilon)$" includes that the integral in (5) exists: the denominator is non-zero on $(0,u)$, its reciprocal is integrable, and $g$ is integrable on $[0,u]$. The $o(\sqrt u)$ term is the little-o of $\sqrt u$ along $u\to0^+$. This $\alpha$ is not the $\alpha=\mu/\sigma$ of p. 895 and of the proof of Theorem 2.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 898, Lemma 4

import Mathlib
import Definitions.Def_SchmidliRuin_Exist_Setting

namespace SchmidliRuin.Exist

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

/-- Lemma 4 (Schmidli 2002, p. 898): local existence of a solution of (5) near `0`, with
`g(u) = λ/c - α√u + o(√u)`, `α = λµ/(σc^{3/2})`. -/
theorem lemma_4
    (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : SchmidliRuin.Verif.ReinsPremium c cb) (hν : SchmidliRuin.Verif.ClaimLaw ν)
    (hdens : HasBoundedDensity ν) :
    ∃ ε > 0, ∃ g : ℝ → ℝ, SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g (Ico 0 ε) ∧
      (fun u => g u - (lam / c - lam * mu / (sigma * c ^ ((3 : ℝ) / 2)) * Real.sqrt u))
        =o[𝓝[>] 0] (fun u => Real.sqrt u) := by sorry

end SchmidliRuin.Exist
