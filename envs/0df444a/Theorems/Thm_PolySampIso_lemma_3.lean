-- Prove2me | Theorems.Thm_PolySampIso_lemma_3
-- name    : PolySampIso.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:38.442423+00:00
-- url     : https://prove2.me/theorems/98050121-6e4d-454b-9d71-92b09638da82
-- title:
--   Lemma 3 and Remark 2, p.13 — every log-concave measure on X satisfies a 1/(16m)-ψ-PI
-- statement:
--   Let $X=\{Ax<b\}$ be a nonempty bounded polytope with $m$ constraints and $\psi$ its log barrier. Let $g\ge0$ be a log-concave density supported on $X$ (so $g(\lambda x+(1-\lambda)y)\ge g(x)^\lambda g(y)^{1-\lambda}$ on $X$) with $\int g=1$, and $\mu=g\,dx$. Then $\mu$ satisfies a $\tfrac1{16m}$-$\psi$-PI:
--
--   $$\mathrm{Var}_\mu[f]\le16m\,\mathbb E_\mu\big[\|\nabla f\|^2_{H^{-1}}\big]\quad\text{for every smooth }f:X\to\mathbb R.$$
--
--   With $g=\mathbb 1_X/\mathrm{vol}(X)$ this is Lemma 3 for the uniform measure $\pi$; the extension (Remark 2) covers every cooled measure $\pi_t$. The constant $1/(16m)$ is the isoperimetry the title refers to: the final sampler's iteration count matches it up to logarithmic factors.
--
--   Differences from the source:
--   - generalization: Lemma 3: π satisfies a 1/(16m)-ψ-PI → every probability measure g·dx with g a log-concave density supported on X; reason: this is the paper's Remark 2; it specializes to Lemma 3 at g = 𝕀_X/vol(X)
--   - reading: Remark 2: any log-concave measure π supported on X → a measure with a log-concave Lebesgue density vanishing off X; reason: Remark 2's argument rests on [LV07] Theorem 2.5, which is stated for log-concave densities; this is the class the paper uses (π_t)
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 3 and Remark 2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_PsiPI
import Definitions.Def_PolySampIso_LogConcave

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Lemma 3 with Remark 2** (every log-concave measure on the polytope satisfies a
`1/(16m)`-ψ-PI for the log barrier).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 3 and Remark 2, p.13 (PDF p.15):

"Lemma 3. π satisfies a 1/(16m)-ψ-PI (Definition 2)."
"Remark 2. The conclusion of Lemma 3 extends to any log-concave measure π supported on X. To see
this, Theorem 2.5 of [LV07] extends Theorem 1, [Lov99] as cited in the proof of Lemma 3 to arbitrary
log-concave π, which is the only step that actually used the specific measure."

**Formalization Note.** The item states Remark 2's form, which contains Lemma 3 (take
`g = 𝕀_X/vol(X)`, the density of the uniform measure `π`). A log-concave measure supported on `X`
is `volume.withDensity g` for a log-concave density `g ≥ 0` vanishing off `X`
(`IsLogConcaveDensityOn`), the form of the cited [LV07] Theorem 2.5. `ψ` is the log barrier (7) on
`X = {Ax < b}` under the standing assumption of §2.3. -/
theorem lemma_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hX : StandingAssumption A b) (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : IsLogConcaveDensityOn (polytope A b) g)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : μ = volume.withDensity fun x => ENNReal.ofReal (g x)) [IsProbabilityMeasure μ] :
    SatisfiesPsiPI μ (polytope A b) (logBarrier A b) (1 / (16 * m)) := by sorry

end PolySampIso
