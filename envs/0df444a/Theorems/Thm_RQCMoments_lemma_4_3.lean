-- Prove2me | Theorems.Thm_RQCMoments_lemma_4_3
-- name    : RQCMoments.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:20.516143+00:00
-- url     : https://prove2.me/theorems/d2f3c0cb-ee83-48b9-9253-e54567a8ef38
-- title:
--   Lemma 4.3 — uniform exponential Christoffel bound $\sup_{u\ge0}\lambda_{\omega,\ell}(u)\le C/\sqrt\ell$
-- statement:
--   Let $\omega$ be the mean-one exponential probability measure, $d\omega(t)=e^{-t}\,dt$ on $[0,\infty)$. There is an absolute constant $C>0$ such that for every integer $\ell\ge 1$
--   $$
--   \sup_{u\ge 0}\lambda_{\omega,\ell}(u)\le\frac{C}{\sqrt{\ell}} .
--   $$
--
--   The uniformity in $u$ matters: Theorem 4.4 applies it at the points $Dx_i$, which are not confined to $[0,1]$.
--
--   Differences from the source:
--
--   - encoding: sup_{u≥0} λ_{ω,ℓ}(u) ≤ C/√ℓ → ∃ C > 0, ∀ ℓ ≥ 1, ∀ u ≥ 0, christoffel ω ℓ u ≤ C/√ℓ; reason: a bound on a supremum is a bound at every point; C is chosen before ℓ and u
--   - encoding: dω(t) = e^{−t} dt on [0, ∞) → ProbabilityTheory.expMeasure 1; reason: Mathlib's exponential law with rate 1 has exactly this density
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.3, (59), p.23 (PDF p.25)

import Mathlib
import Definitions.Def_RQCMoments_christoffel

set_option autoImplicit false

namespace RQCMoments

/-- **Lemma 4.3** (uniform exponential Christoffel bound) (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.3, p.23, PDF p.25).
For the mean-one exponential probability measure `ω`, `dω(t) = e^{−t} dt` on `[0, ∞)`, there is
an absolute constant `C > 0` such that for every integer `ℓ ≥ 1`,
`sup_{u≥0} λ_{ω,ℓ}(u) ≤ C/√ℓ` (59).

**Formalization Note** `ω` is Mathlib's `ProbabilityTheory.expMeasure 1` (density `e^{−t}` on
`t ≥ 0`). The supremum bound is written as a bound for every `u ≥ 0`; `C` is chosen before `ℓ`
and `u`. -/
theorem lemma_4_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ u : ℝ, 0 ≤ u →
      christoffel (ProbabilityTheory.expMeasure 1) ℓ u ≤ C / Real.sqrt ℓ := by sorry

end RQCMoments
