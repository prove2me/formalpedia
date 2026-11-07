-- Prove2me | Theorems.Thm_PsdPermanent_lemma_4
-- name    : PsdPermanent.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:13.427193+00:00
-- url     : https://prove2.me/theorems/7e0617d1-eafc-4125-8054-87cd36034856
-- title:
--   Lemma 4 — Gibbs variational formula
-- statement:
--   Let $U:\mathbb C^d\to\mathbb R\cup\{-\infty\}$ be measurable and assume that $Z_U=\pi^{-d}\int_{\mathbb C^d}\exp(U(z)-z^\dagger z)\,dz$ is finite and positive. Let $\mathcal A_U$ be the class of probability densities $\mu$ for which $\mathbb E_\mu[Z^\dagger Z]<\infty$, $h(\mu)$ is well-defined and $\mathbb E_\mu[U(Z)]$ is well-defined, so that the expression below has no indeterminate form. If the Gibbs density proportional to $\exp(U(z)-z^\dagger z)$ belongs to $\mathcal A_U$, then
--   $$\log Z_U=\sup\big\{\mathbb E_\mu[U(Z)]-\mathbb E_\mu[Z^\dagger Z]+h(\mu)-d\log\pi\ \big|\ \mu\in\mathcal A_U\big\}.$$
--
--   Both bounds of Theorem 7 are read off this formula.
--
--   Differences from the source:
--   - encoding: U : C^d → R ∪ {−∞} → U into EReal with U z ≠ ⊤ at every z; reason: the same set of values
--   - encoding: a probability density → a Borel function, nonnegative at every point, of total mass one; reason: every density has such a version; all quantities depend only on its a.e. class
--   - encoding: h, a real number or ±∞ when well-defined → an EReal built from two lintegrals, with the predicate EntropyWellDefined; reason: a Bochner integral would read h = −∞ as 0
--   - encoding: the supremum, a value in the extended reals → IsLUB in EReal, with log Z_U = ENNReal.log of Z_U; reason: the least upper bound is the supremum
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 4, p.5

import Mathlib
import Definitions.Def_PsdPermanent_secondMoment
import Definitions.Def_PsdPermanent_gibbsDensity
import Definitions.Def_PsdPermanent_Admissible

namespace PsdPermanent

/-- **Lemma 4 (Gibbs variational formula).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 4, p.5: "Let U : C^d → R ∪ {−∞} be measurable and assume Z_U = π^{−d} ∫_{C^d} exp(U(z) − z†z) dz is finite
and positive. Let A_U be the set of probability densities µ on C^d for which E_µ[Z†Z] < ∞, h(µ) is well-defined, and
E_µ[U(Z)] is well-defined, so that the expression below has no indeterminate ∞ − ∞ form. Then log Z_U =
sup{E_µ[U(Z)] − E_µ[Z†Z] + h(µ) − d log π | µ ∈ A_U}, provided the Gibbs density proportional to exp(U(z) − z†z)
belongs to A_U."

**Formalization Note.** `U` is `EReal`-valued, never `⊤`. The supremum is an `IsLUB` in `EReal`, and `log Z_U` is
`ENNReal.log`. See `PsdPermanent.Admissible` for the guard against `⊤ + ⊥ = ⊥`. -/
theorem lemma_4 {d : ℕ} (U : (Fin d → ℂ) → EReal) (hU : Measurable U) (hUtop : ∀ z, U z ≠ ⊤)
    (hZ0 : partitionZ U ≠ 0) (hZtop : partitionZ U ≠ ⊤) (hgibbs : Admissible U (gibbsDensity U)) :
    IsLUB {v : EReal | ∃ f : (Fin d → ℂ) → ℝ, Admissible U f ∧ v = gibbsObjective U f}
      (ENNReal.log (partitionZ U)) := by sorry

end PsdPermanent
