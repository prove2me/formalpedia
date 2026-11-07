-- Prove2me | Theorems.Thm_PsdPermanent_lemma_2
-- name    : PsdPermanent.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:14.371348+00:00
-- url     : https://prove2.me/theorems/db01af68-7552-4452-9b97-05cb339188c9
-- title:
--   Lemma 2 — real Gaussian maximum entropy
-- statement:
--   Let $Y$ be an $\mathbb R^k$-valued random vector with a density, finite second moment and nonsingular covariance matrix $\Sigma=\mathbb E[(Y-\mathbb E[Y])(Y-\mathbb E[Y])^\top]$. Then $h(Y)$ is well-defined and
--   $$h(Y)\le\frac12\log\det(2\pi e\,\Sigma)=\frac12\log\big[(2\pi e)^k\det\Sigma\big].$$
--   Equality holds if and only if $Y$ is distributed as $N(\mathbb E[Y],\Sigma)$.
--
--   This is the classical maximum-entropy property of the Gaussian, applied below to the real and imaginary parts of a complex vector.
--
--   Differences from the source:
--   - encoding: a probability density → a Borel function, nonnegative at every point, of total mass one; reason: every density has such a version; all quantities depend only on its a.e. class
--   - encoding: h, a real number or ±∞ when well-defined → an EReal built from two lintegrals, with the predicate EntropyWellDefined; reason: a Bochner integral would read h = −∞ as 0
--   - encoding: Y is distributed as N(E[Y], Σ) → the density equals the Gaussian density almost everywhere; reason: two densities define the same law exactly when they agree almost everywhere
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 2, p.4

import Mathlib
import Definitions.Def_PsdPermanent_IsProbDensity
import Definitions.Def_PsdPermanent_entropy
import Definitions.Def_PsdPermanent_realCovariance
import Definitions.Def_PsdPermanent_realGaussianDensity
open MeasureTheory

namespace PsdPermanent

/-- **Lemma 2 (Real Gaussian maximum entropy).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 2, p.4: "Let Y be an R^k-valued random vector with density, finite second moment, and
nonsingular covariance matrix Σ = E[(Y − E[Y])(Y − E[Y])^⊤]. Then h(Y) ≤ (1/2) log det(2πe Σ) =
(1/2) log[(2πe)^k det Σ]. Equality holds if and only if Y is distributed as N(E[Y], Σ)."

**Formalization Note.** `h` is `EReal`-valued (`PsdPermanent.entropy`) and may be `−∞`; the statement concludes that
it is well-defined. "Distributed as" is almost-everywhere equality of densities. -/
theorem lemma_2 {k : ℕ} (f : (Fin k → ℝ) → ℝ) (hf : IsProbDensity f) (h2 : FiniteSecondMomentReal f)
    (hS : (realCovariance f).det ≠ 0) :
    EntropyWellDefined f ∧
      entropy f ≤
        ((1 / 2 * Real.log (((2 * Real.pi * Real.exp 1) • realCovariance f).det) : ℝ) : EReal) ∧
      1 / 2 * Real.log (((2 * Real.pi * Real.exp 1) • realCovariance f).det) =
        1 / 2 * Real.log ((2 * Real.pi * Real.exp 1) ^ k * (realCovariance f).det) ∧
      (entropy f = ((1 / 2 * Real.log ((2 * Real.pi * Real.exp 1) ^ k * (realCovariance f).det) : ℝ) : EReal) ↔
        f =ᵐ[volume] realGaussianDensity (realMean f) (realCovariance f)) := by sorry

end PsdPermanent
