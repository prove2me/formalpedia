-- Prove2me | Theorems.Thm_PrivateRelease_VCLowerBound_theorem_3_11
-- name    : PrivateRelease.VCLowerBound.theorem_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:41.171879+00:00
-- url     : https://prove2.me/theorems/76a1cb7d-7a8a-45ea-a8ea-f916e463eff4
-- title:
--   Theorem 3.11 — an ε-DP mechanism (α, δ)-useful for C on databases of size n ≤ VCDIM(C)/2 has α ≥ Ω(1/(4+16ε))
-- statement:
--   The paper writes $\Omega(\cdot)$; here it is an absolute constant. There is a constant $c > 0$ with the following property. Let $X$ be any data universe, $C$ any class of predicates $\varphi : X \to \{0,1\}$ (identified with their counting queries), and $n \ge 1$ with
--
--   $$n \le \frac{\mathrm{VCDIM}(C)}{2}.$$
--
--   Let $0 \le \epsilon \le 1$ and $0 < \delta \le 1/4$. Let $M$ be a mechanism mapping each input database $z \in X^n$ to a probability distribution on an output space $O$, with a readout $\mathrm{ans}$ that is measurable in the output for every $\varphi \in C$. If $M$ is $\epsilon$-differentially private and $(\alpha,\delta)$-useful for $C$, then
--
--   $$\alpha \ \ge\ \frac{c}{4 + 16\epsilon}.$$
--
--   In words: on databases smaller than half the VC-dimension of $C$, no differentially private mechanism can answer every query of $C$ to within a constant error. Together with the paper's upper bound (the net mechanism, useful once $n$ grows linearly in $\mathrm{VCDIM}(C)$), this shows that the dependence of the sample size on the VC-dimension is necessary.
--
--   **Formalization Note** The constant $c$ is quantified before the universe, the class, the size and the mechanism, so it is absolute. The paper's hypothesis "$0 < \delta < 1$ bounded away from $1$ by a constant" is not what its proof supports: keeping the failure probability $\delta$, the proof gives $(1-\delta)(1-2\alpha) \le e^{\epsilon}(\delta+2\alpha)$, which bounds $\alpha$ away from $0$ only when $\delta < 1/(1+e^{\epsilon})$ (about $0.27$ at $\epsilon = 1$). The explicit threshold $\delta \le 1/4$ is used instead. Neighbouring databases differ in exactly one entry (the paper's "$|D\Delta D'| \le 1$" read as replace-one). Mechanisms are arbitrary measurable-output randomized maps (the paper's synthetic-database mechanisms are a special case). $n \ge 1$ excludes the empty database, on which every mechanism is private. VC-dimension is $\mathbb N \cup \{\infty\}$-valued.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 11, Theorem 3.11 (proof pp. 11–12)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_PrivateRelease_VCLowerBound_Queries

namespace PrivateRelease.VCLowerBound

open MeasureTheory

/-- Theorem 3.11 (p. 11). There is an absolute constant `c > 0` such that: for every data universe
`X`, every class `C` of counting queries (predicates `X → Bool`), every `n ≥ 1` with
`n ≤ VCDIM(C)/2`, every `0 ≤ ε ≤ 1` and every `0 < δ ≤ 1/4`, if `M` is an `ε`-differentially
private mechanism (replace-one neighbours; outputs are probability measures on `O`, read by a readout
`ans` measurable in the output for each query of `C`) that is `(α, δ)`-useful for `C` on databases of
size `n`, then `α ≥ c / (4 + 16ε)`.

The paper's `Ω(·)` is the absolute constant `c`; its "δ bounded away from 1 by a constant" is
instantiated as `δ ≤ 1/4`, the range the proof supports (it needs `δ < 1/(1 + e^ε)`). -/
theorem theorem_3_11 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X : Type) (C : Set (X → Bool)) (n : ℕ) (O : Type) [MeasurableSpace O]
        (M : (Fin n → X) → Measure O) (ans : O → (X → Bool) → ℝ) (ε α δ : ℝ),
        1 ≤ n → ((2 * n : ℕ) : ℕ∞) ≤ HighDimProb.Chaining.vcDim C →
        0 ≤ ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        (∀ z, IsProbabilityMeasure (M z)) →
        (∀ φ ∈ C, Measurable fun o => ans o φ) →
        PrivLearn.Generic.IsDP M ε → IsUseful C α δ M ans →
        c / (4 + 16 * ε) ≤ α := by sorry

end PrivateRelease.VCLowerBound
