-- Prove2me | Theorems.Thm_PrivLearn_Generic_corollary_3_6
-- name    : PrivLearn.Generic.corollary_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:54.966981+00:00
-- url     : https://prove2.me/theorems/c22b0575-d8ce-427a-a356-d225d9aa5b10
-- title:
--   Corollary 3.6 — private agnostic learning from $O((\mathrm{VCDIM}(C_d)\ln|X_d|+\ln\frac1\beta)\max\{\frac1{\varepsilon\alpha},\frac1{\alpha^2}\})$ examples
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $X$ be a finite set of examples, $H=C_d$ a nonempty class of concepts $X\to\{0,1\}$ of VC dimension $\mathrm{VCDIM}(C_d)$ (the cardinality of a largest set $S\subseteq X$ on which $C_d$ realizes all $2^{|S|}$ labelings, Definition 3.5), and let $\varepsilon>0$ and $\alpha,\beta\in(0,1/2)$. Then the exponential mechanism $\mathcal A^{\varepsilon}_q$ over $H$ is $\varepsilon$-differentially private for every database size, and for every probability distribution $P$ on $X\times\{0,1\}$ and every $n$ with
--
--   $$n\ \ge\ C\Big(\mathrm{VCDIM}(C_d)\cdot\ln|X|+\ln\frac1\beta\Big)\cdot\max\Big\{\frac1{\varepsilon\alpha},\frac1{\alpha^2}\Big\},$$
--
--   on $n$ i.i.d. examples from $P$ it outputs a hypothesis $h$ with $\mathrm{err}(h)>\mathrm{OPT}+\alpha$ with probability at most $\beta$.
--
--   The corollary replaces the cardinality of the class by its VC dimension, at the price of a logarithmic dependence on the size of the domain.
--
--   **Formalization Note.** Since $X$ is finite, $C_d$ is a finite set of functions and is its own set of distinct labelings of $X$, so the learner of the paper's proof is $\mathcal A^{\varepsilon}_q$ over $H=C_d$ itself. The VC dimension is the platform's `ComputationalLearning.vcDim` (Kearns–Vazirani, Definition 9: the supremum of the sizes of shattered finite sets, in $\mathbb N\cup\{\infty\}$), which is finite here and is converted to a natural number. $O(\cdot)$ is an absolute constant $C$ chosen before every other quantity. For $|X|\le1$ Lean's $\ln$ gives $0$ (for $|X|=0$ by the convention $\ln0=0$), and the bound reduces to $C\ln(1/\beta)\max\{\dots\}$, which is still sufficient because then $|H|\le2$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 13, Corollary 3.6 (Definition 3.5 for VCDIM)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Generic_ExpMech
import Definitions.Def_ComputationalLearning_VC

open MeasureTheory

namespace PrivLearn.Generic

/-- Corollary 3.6 (p. 13). There is an absolute constant `C > 0` such that for every finite
example domain `X`, every nonempty class `H = C_d` of concepts `X → {0,1}` of VC dimension
`d = VCDIM(C_d)` and all `ε > 0`, `α, β ∈ (0, 1/2)`, the exponential mechanism `A^ε_q` on `H` is
`ε`-differentially private and agnostically learns `H` (error `> OPT + α` with probability at most
`β`) from every `n ≥ C (d ln|X| + ln(1/β)) max{1/(εα), 1/α²}` examples. -/
theorem corollary_3_6 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type) [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
        (H : Finset (X → Bool)) (hH : H.Nonempty) (ε α β : ℝ),
        0 < ε → 0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
        (∀ n : ℕ, IsDP (fun z : Fin n → X × Bool => expMech H ε z) ε) ∧
        ∀ (P : Measure (X × Bool)) [IsProbabilityMeasure P] (n : ℕ),
          C * ((ComputationalLearning.vcDim (H : Set (X → Bool))).toNat
                * Real.log (Fintype.card X) + Real.log (1 / β))
            * max (1 / (ε * α)) (1 / α ^ 2) ≤ n →
          ∫⁻ z, expMech H ε z {h | OPT P H hH + α < err P h} ∂(Measure.pi fun _ : Fin n => P)
            ≤ ENNReal.ofReal β := by sorry

end PrivLearn.Generic
