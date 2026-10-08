-- Prove2me | Theorems.Thm_PrivateRelease_VCLowerBound_theorem_3_11_explicit
-- name    : PrivateRelease.VCLowerBound.theorem_3_11_explicit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:34.912391+00:00
-- url     : https://prove2.me/theorems/7ec59035-5be3-45e1-8833-7573861e21c8
-- title:
--   Theorem 3.11, proof (p. 12) — $(1-\delta)(1-2\alpha) \le e^{\epsilon}(\delta + 2\alpha)$ for private useful mechanisms on databases of size $n \le \mathrm{VCDIM}(C)/2$
-- statement:
--   Let $C$ be a class of predicates on a data universe $X$, and let $n \ge 1$ satisfy $2n \le \mathrm{VCDIM}(C)$. Let $M$ be a mechanism that maps each input database $z \in X^n$ to a probability distribution $M(z)$ on an output space $O$, and let $\mathrm{ans}$ be a readout such that $o \mapsto \mathrm{ans}(o,\varphi)$ is measurable for every $\varphi \in C$. Suppose that
--
--   1. $M$ is $\epsilon$-differentially private: $\Pr[M(z) \in E] \le e^{\epsilon}\Pr[M(z') \in E]$ for every measurable $E \subseteq O$ and all inputs $z, z'$ that differ in exactly one entry;
--   2. $M$ is $(\alpha,\delta)$-useful for $C$, with $0 < \delta < 1$.
--
--   Then
--
--   $$(1-\delta)(1-2\alpha) \ \le\ e^{\epsilon}\,(\delta + 2\alpha).$$
--
--   Equivalently $\alpha \ge \dfrac{(1-\delta) - e^{\epsilon}\delta}{2\,(1 - \delta + e^{\epsilon})}$, a positive lower bound on the error whenever $\delta < 1/(1+e^{\epsilon})$. This is the inequality that the final display of the paper's proof derives; Theorem 3.11 follows from it.
--
--   **Formalization Note** The paper's display reads $\exp(2\epsilon) \ge \Pr[x \in T']/\Pr[x \in \hat T'] \ge (1-2\alpha)/(2\alpha)$: it counts $|T \Delta \hat T| = 2$ under the neighbour relation $|D \Delta D'| \le 1$, and it drops the failure probability $\delta$ of the two reconstructions. Here neighbours are databases differing in one entry (replace-one), under which $T$ and $\hat T = (T\setminus\{x\}) \cup \{y\}$ are neighbours, so the factor is $e^{\epsilon}$; and $\delta$ is kept. VC-dimension is the $\mathbb N \cup \{\infty\}$-valued supremum of the sizes of shattered sets, so $2n \le \mathrm{VCDIM}(C)$ also covers infinite VC-dimension. The measurability of the readouts is needed: without it a mechanism into a trivial $\sigma$-algebra is $0$-private and the bound fails.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 12, proof of Theorem 3.11 (final display)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_PrivateRelease_VCLowerBound_Queries

namespace PrivateRelease.VCLowerBound

open MeasureTheory

/-- Theorem 3.11, proof (p. 12), with `δ` kept. Let `C` be a class of predicates on `X` and `n ≥ 1`
with `2n ≤ VCDIM(C)`. Let `M` be a mechanism on input databases of size `n` whose outputs are
probability measures on `O`, with a readout `ans` that is measurable in the output for each query of
`C`. If `M` is `ε`-differentially private (replace-one neighbours) and `(α, δ)`-useful for `C` with
`0 < δ < 1`, then `(1 − δ)(1 − 2α) ≤ e^ε (δ + 2α)`. -/
theorem theorem_3_11_explicit {X O : Type} [MeasurableSpace O] (C : Set (X → Bool)) (n : ℕ)
    (M : (Fin n → X) → Measure O) (ans : O → (X → Bool) → ℝ) (ε α δ : ℝ)
    (hn : 1 ≤ n) (hvc : ((2 * n : ℕ) : ℕ∞) ≤ HighDimProb.Chaining.vcDim C)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hprob : ∀ z, IsProbabilityMeasure (M z))
    (hans : ∀ φ ∈ C, Measurable fun o => ans o φ)
    (hdp : PrivLearn.Generic.IsDP M ε) (huse : IsUseful C α δ M ans) :
    (1 - δ) * (1 - 2 * α) ≤ Real.exp ε * (δ + 2 * α) := by sorry

end PrivateRelease.VCLowerBound
