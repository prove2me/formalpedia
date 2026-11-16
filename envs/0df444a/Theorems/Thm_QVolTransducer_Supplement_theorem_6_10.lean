-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_6_10
-- name    : QVolTransducer.Supplement.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:42:17.497289+00:00
-- url     : https://prove2.me/theorems/3f9008a9-6d0f-43dc-b8f6-736a385a5201
-- title:
--   Theorem 6.10 — conductance under perturbation (corrected: final '>' holds for 0 < φ(P) < ∞)
-- statement:
--   Let $(\Omega,\Sigma)$ be a measurable space with $\Sigma$ countably generated, and let $(\Omega,P)$ and $(\Omega,P')$ be random walks with stationary probability measures $\pi$ and $\pi'$, $\pi'\ll\pi$. Suppose that for every $x\in\Omega$
--
--   $$\|P(x,\cdot)-P'(x,\cdot)\|_{\mathrm{TV}}\le\eta,\qquad\Big|\frac{d\pi'}{d\pi}-1\Big|\le\xi<\frac14\ \text{ a.s. on }\operatorname{supp}(\pi').$$
--
--   Then
--
--   $$\varphi(P')\ge\varphi(P)\,\frac{1-\xi}{2(1+\xi)}-\eta\ \ge\ \frac{3\varphi(P)}{10}-\eta,$$
--
--   and the second inequality is strict whenever $0<\varphi(P)<\infty$.
--
--   Conductance is therefore robust under small perturbations of the transition kernel and of the stationary measure, which is how the paper transfers the speedy-walk conductance bound to its discretizations.
--
--   **Formalization Note** Conductances lie in $[0,\infty]$, so the first inequality is stated as $\varphi(P)(1-\xi)/(2(1+\xi))\le\varphi(P')+\eta$. The total variation bound is $|P(x,A)-P'(x,A)|\le\eta$ for every measurable $A$.
--
--   Differences from the source:
--   - correction: φ(P)(1 − ξ)/(2(1 + ξ)) − η > 3φ(P)/10 − η → ≥ always, and > when 0 < φ(P) < ∞; reason: false at φ(P) = 0, where both sides equal −η: Ω = ℕ with Σ = 2^ℕ, P = P′ the Metropolis nearest-neighbour walk with target π_n ∝ 1/(n+1)², π′ = π, ξ = 0, η ≥ 0; it is reversible and irreducible, and the tail sets {n ≥ k} have flow/mass → 0, so φ(P) = 0
--   - encoding: φ(P′) ≥ φ(P)(1 − ξ)/(2(1 + ξ)) − η with conductances in [0, ∞] → (1 − ξ)/(2(1 + ξ)) · φ(P) ≤ φ(P′) + η in ℝ≥0∞, and the strict comparison in ℝ for finite φ(P); reason: avoids truncated subtraction in [0, ∞]; same content
--   - encoding: ‖P(x, ·) − P′(x, ·)‖_TV ≤ η → |P(x, A) − P′(x, A)| ≤ η for every measurable A; reason: the total variation distance of probability measures is sup_A |P(x, A) − P′(x, A)|
--   - reading: |dπ′/dπ − 1| ≤ ξ a.s. on supp(π′) → π′-almost everywhere, with the Radon–Nikodym derivative π′.rnDeriv π; reason: the support of π′ carries all of its mass
--   - encoding: a measure space (Ω, Σ, µ) → a measurable space (µ omitted); reason: µ appears in no hypothesis or conclusion of this theorem
--   - encoding: random walks with stationary measures → Markov kernels with IsMarkovKernel and stationary probability measures (Definition 6.1: πP = π); reason: Definition 6.1
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 6.10, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_QVolTransducer_Supplement_measCond

namespace QVolTransducer.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Conductance under perturbation** (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Theorem 6.10, p.42 (PDF p.44); corrected: the final strict inequality
needs `0 < φ(P) < ∞`).

Let `(Ω, Σ)` be a measurable space with `Σ` countably generated, and `(Ω, P)`, `(Ω, P′)` random walks
with stationary probability measures `π`, `π′`, `π′ ≪ π`. Suppose that for every `x ∈ Ω`,
`‖P(x, ·) − P′(x, ·)‖_TV ≤ η`, and `|dπ′/dπ − 1| ≤ ξ < 1/4` almost surely on `supp(π′)`. Then
`φ(P′) ≥ φ(P)(1 − ξ)/(2(1 + ξ)) − η ≥ 3φ(P)/10 − η`, and the second inequality is strict when
`0 < φ(P) < ∞`.

**Formalization Note** Conductances (Definition 6.6) take values in `[0, ∞]`, so the first
inequality is written `φ(P)(1 − ξ)/(2(1 + ξ)) ≤ φ(P′) + η` in `ℝ≥0∞`; the second is
`3/10 · φ(P) ≤ (1 − ξ)/(2(1 + ξ)) · φ(P)`, and its strict version, for finite positive `φ(P)`,
is stated in `ℝ` with the `− η` on both sides. The paper's final `>` is false when `φ(P) = 0`
(both sides equal `−η`): this is the correction. The total-variation bound is
`|P(x, A) − P′(x, A)| ≤ η` for every measurable `A`, which is `sup_A |P(x, A) − P′(x, A)| ≤ η`.
"A.s. on `supp(π′)`" is `π′`-almost everywhere. The measure `µ` of the printed measure space plays no
role in the statement and is omitted. -/
theorem theorem_6_10 {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace.CountablyGenerated Ω]
    (P P' : Kernel Ω Ω) [IsMarkovKernel P] [IsMarkovKernel P'] (π π' : Measure Ω)
    [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hstat : IsStationaryWrt (fun x => P x) π) (hstat' : IsStationaryWrt (fun x => P' x) π')
    (hac : π' ≪ π) (η ξ : ℝ)
    (htv : ∀ x (A : Set Ω), MeasurableSet A → |(P x A).toReal - (P' x A).toReal| ≤ η)
    (hrn : ∀ᵐ x ∂π', |(π'.rnDeriv π x).toReal - 1| ≤ ξ) (hξ : ξ < 1 / 4) :
    ENNReal.ofReal ((1 - ξ) / (2 * (1 + ξ))) * measCond (fun x => P x) π ≤
        measCond (fun x => P' x) π' + ENNReal.ofReal η ∧
      ENNReal.ofReal (3 / 10) * measCond (fun x => P x) π ≤
        ENNReal.ofReal ((1 - ξ) / (2 * (1 + ξ))) * measCond (fun x => P x) π ∧
      (0 < measCond (fun x => P x) π → measCond (fun x => P x) π < ⊤ →
        3 * (measCond (fun x => P x) π).toReal / 10 - η <
          (measCond (fun x => P x) π).toReal * ((1 - ξ) / (2 * (1 + ξ))) - η) := by sorry

end QVolTransducer.Supplement
