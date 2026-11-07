-- Prove2me | Theorems.Thm_PolySampIso_proposition_6
-- name    : PolySampIso.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:19.229541+00:00
-- url     : https://prove2.me/theorems/a2f44353-77a5-4938-8f5b-c29f6a721ae4
-- title:
--   Proposition 6, p.43 — TV overlap of Metropolis–Hastings kernels ([ALPW24, Lemma 19])
-- statement:
--   Let $(Z,\lambda)$ be a measurable space with a $\sigma$-finite reference measure. Let $P(z,dz')=p(z,z')\lambda(dz')$ be a Markov proposal kernel with symmetric density $p(z,z')=p(z',z)$, and let $\mu=f\lambda$ be a probability measure. Let $M$ be the Metropolis–Hastings kernel
--
--   $$M(z,B)=\int_B a(z,z')P(z,dz')+(1-A(z))\mathbb 1_{z\in B},\qquad a(z,z')=\min\Big\{1,\frac{f(z')}{f(z)}\Big\},\qquad A(z)=\int a(z,z')P(z,dz').$$
--
--   Then for all $z,w$ with $f(z),f(w)>0$,
--
--   $$\mathrm{TV}(M(z,\cdot),M(w,\cdot))\le\mathrm{TV}(P(z,\cdot),P(w,\cdot))+1-\min\{A(z),A(w)\}.$$
--
--   Two Metropolized chains from nearby points thus overlap in one step whenever their proposals overlap and both accept often. In the paper it gives the one-step overlap of Algorithm 6 in the proof of Lemma 32. The Metropolis–Hastings rule is essential: for an arbitrary acceptance function the bound fails.
--
--   Differences from the source:
--   - reading: a symmetric proposal kernel P and target µ ∈ P(Z) with a(z,z′) = min{1, µ(z′)/µ(z)} → P(z, dz′) = p(z, z′)·ref(dz′) with p jointly measurable and symmetric, µ = f·ref, a(z, z′) = min{1, f(z′)/f(z)}, for a σ-finite reference measure ref on Z; reason: (59) is a ratio of densities, which presupposes a reference measure (§2.1 identifies measures with densities); symmetry of P is relative to the same measure
--   - encoding: for all (z, w) ∈ Z × Z → for z, w with f(z), f(w) > 0; reason: a(z, ·) in (59) is undefined when µ(z) = 0
--   - encoding: the Metropolized kernel (58) → the published TierneyMH.Shared.mhKernel with proposal P and acceptance a; reason: it is (58) verbatim for a measurable acceptance with values in [0, 1]
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), (58), (59) and Proposition 6, p.43 (PDF p.45), citing [ALPW24, Lemma 19]

import Mathlib
import Definitions.Def_TierneyMH_Shared_mhKernel
import Definitions.Def_PolySampIso_Divergences

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace PolySampIso

/-- **Proposition 6** (TV overlap of Metropolized kernels, [ALPW24, Lemma 19]).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), (58), (59) and Proposition 6, p.43 (PDF p.45):

"M(z, B) := ∫_B a(z, z′)P(z, dz′) + (1 − A(z))I{z∈B}, A(z) := Ez′∼P(z,·)[a(z, z′)]. (58)"
"We focus on the Metropolis-Hastings rule for symmetric P, where for a target measure µ,
a(z, z′) := min{1, µ(z′)/µ(z)}. (59)"
"Proposition 6 (Lemma 19, [ALPW24]). Let M : Z × B(Z) → [0, 1] be a Metropolized kernel (58), (59)
with respect to a symmetric proposal kernel P : Z × B(Z) → [0, 1] and target measure µ ∈ P(Z), and
define the total acceptance probabilities A : Z → [0, 1] as in (58). Then for all (z, w) ∈ Z × Z,
TV(M(z, ·), M(w, ·)) ≤ TV(P(z, ·), P(w, ·)) + 1 − min {A(z), A(w)} ."

**Formalization Note.**
* Measures are identified with densities with respect to a reference measure (§2.1): here a
  σ-finite measure `ref` on `Z`. The proposal is `P(z, dz′) = p(z, z′) ref(dz′)` with `p` jointly
  measurable, `∫ p(z, ·) d ref = 1` and `p(z, z′) = p(z′, z)` (symmetric); the target is
  `µ = f · ref`, a probability density `f ≥ 0`. `M` is the published `TierneyMH.Shared.mhKernel` (58) with the MH acceptance
  (59) `a(z, z′) = min{1, f(z′)/f(z)}`, and `A(z) = ∫ a(z, ·) dP(z, ·)`.
* (59) is defined at `z` only when `µ(z) > 0`, so the two points satisfy `f(z), f(w) > 0`.
* The MH rule matters: for an arbitrary acceptance function the bound fails. -/
theorem proposition_6 {Z : Type*} [MeasurableSpace Z] (ref : Measure Z) [SigmaFinite ref]
    (p : Z → Z → ℝ≥0) (hp : Measurable (Function.uncurry p))
    (hpsymm : ∀ z z', p z z' = p z' z) (hpm : ∀ z, ∫⁻ z', (p z z' : ℝ≥0∞) ∂ref = 1)
    (f : Z → ℝ) (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    (hf1 : ∫⁻ z, ENNReal.ofReal (f z) ∂ref = 1)
    (z w : Z) (hz : 0 < f z) (hw : 0 < f w) :
    let P : Kernel Z Z := Kernel.withDensity (Kernel.const Z ref) fun z z' => (p z z' : ℝ≥0∞)
    let a : Z × Z → ℝ≥0∞ := fun q => ENNReal.ofReal (min 1 (f q.2 / f q.1))
    let M : Kernel Z Z := TierneyMH.Shared.mhKernel P a
    let Acc : Z → ℝ := fun z => ∫ z', min 1 (f z' / f z) ∂(P z)
    tvDist (M z) (M w) ≤ tvDist (P z) (P w) + 1 - min (Acc z) (Acc w) := by sorry

end PolySampIso
