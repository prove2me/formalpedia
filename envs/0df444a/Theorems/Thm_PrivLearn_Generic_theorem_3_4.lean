-- Prove2me | Theorems.Thm_PrivLearn_Generic_theorem_3_4
-- name    : PrivLearn.Generic.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:54.984142+00:00
-- url     : https://prove2.me/theorems/f9d8daab-3cbf-4b08-a2c1-0cfe672cebd4
-- title:
--   Theorem 3.4 — the generic private learner agnostically learns any finite class from $O((\ln|\mathcal H_d|+\ln\frac1\beta)\max\{\frac1{\varepsilon\alpha},\frac1{\alpha^2}\})$ examples
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $X$ be a finite set of examples, $H=C_d$ a finite nonempty class of hypotheses $X\to\{0,1\}$, and let $\varepsilon>0$ and $\alpha,\beta\in(0,1/2)$. Then the exponential mechanism $\mathcal A^{\varepsilon}_q$ over $H$ satisfies:
--
--   1. **Privacy.** For every database size $n$, $\mathcal A^{\varepsilon}_q$ is $\varepsilon$-differentially private.
--   2. **Utility.** For every probability distribution $P$ on $X\times\{0,1\}$ and every $n$ with
--   $$n\ \ge\ C\Big(\ln|H|+\ln\frac1\beta\Big)\cdot\max\Big\{\frac1{\varepsilon\alpha},\frac1{\alpha^2}\Big\},$$
--   if $z$ consists of $n$ examples drawn i.i.d. from $P$, then
--   $$\Pr\big[\mathrm{err}(\mathcal A^{\varepsilon}_q(z))>\mathrm{OPT}+\alpha\big]\le\beta,$$
--   where $\mathrm{OPT}=\min_{f\in H}\mathrm{err}(f)$ and the probability is over $z$ and the coins of the mechanism.
--
--   This is the quantitative ("More precisely") form of Theorem 3.4: every finite concept class is privately agnostically learnable with sample size logarithmic in its cardinality. The qualitative first sentence of the theorem (classes of cardinality at most $\exp(\mathrm{poly}(d))$ are privately agnostically learnable) follows, since then $\ln|H|$ is polynomial in $d$.
--
--   **Formalization Note.** The paper writes the sample size as $O(\cdot)$; we state it with one absolute constant $C$, chosen before the domain, the class, the distribution and all parameters. The constant $6$ written at the end of the paper's proof does not make the final inequality close, so no numeric constant is stated. Logarithms are natural. The example domain is a finite type with the discrete σ-algebra (the paper's $X_d$ has representations of size at most $d$), quantified over `Type` so that the existential is well-formed. The learner's output law is a measure on `X → Bool`; the failure probability is the integral over $z\sim P^n$ of the mechanism's probability of the event $\{\mathrm{err}(h)>\mathrm{OPT}+\alpha\}$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 11, Theorem 3.4 (proof pp. 11–12); Definitions 2.5, 3.1, 3.2 on pp. 10

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Generic_ExpMech

open MeasureTheory

namespace PrivLearn.Generic

/-- Theorem 3.4 (p. 11, generic private learner), in its quantitative form. There is an absolute
constant `C > 0` such that for every finite example domain `X`, every finite nonempty class
`H = C_d` of hypotheses `X → {0,1}` and all `ε > 0`, `α, β ∈ (0, 1/2)`, the exponential
mechanism `A^ε_q` (a) is `ε`-differentially private, and (b) for every distribution `P` on
`X × {0,1}` and every
`n ≥ C (ln|H| + ln(1/β)) max{1/(εα), 1/α²}`, run on `n` i.i.d. examples from `P` it outputs a
hypothesis with `err(h) > OPT + α` with probability at most `β`. -/
theorem theorem_3_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type) [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
        (H : Finset (X → Bool)) (hH : H.Nonempty) (ε α β : ℝ),
        0 < ε → 0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
        (∀ n : ℕ, IsDP (fun z : Fin n → X × Bool => expMech H ε z) ε) ∧
        ∀ (P : Measure (X × Bool)) [IsProbabilityMeasure P] (n : ℕ),
          C * (Real.log H.card + Real.log (1 / β)) * max (1 / (ε * α)) (1 / α ^ 2) ≤ n →
          ∫⁻ z, expMech H ε z {h | OPT P H hH + α < err P h} ∂(Measure.pi fun _ : Fin n => P)
            ≤ ENNReal.ofReal β := by sorry

end PrivLearn.Generic
