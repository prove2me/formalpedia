-- Prove2me | Theorems.Thm_PsdPermanent_lemma_3
-- name    : PsdPermanent.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:40.661202+00:00
-- url     : https://prove2.me/theorems/38b96ba8-a9f3-4040-8985-3bd089438535
-- title:
--   Lemma 3 and Eq. (3) — complex entropy bound
-- statement:
--   Let $\mu$ be a probability density on $\mathbb C^d$ with finite second moment, let $Z\sim\mu$, and set $M=\mathbb E_\mu[ZZ^\dagger]$. Then $M\succ0$, the entropy $h(\mu)$ is well-defined, and
--   $$h(\mu)\le d\log\pi+d+\log\det M,$$
--   with equality at $\mathcal{CN}(0,M)$.
--
--   Only the Hermitian second moment is retained, which is what lets the upper bound of Theorem 7 insert $M$ into the relaxation.
--
--   Differences from the source:
--   - encoding: a probability density → a Borel function, nonnegative at every point, of total mass one; reason: every density has such a version; all quantities depend only on its a.e. class
--   - encoding: h, a real number or ±∞ when well-defined → an EReal built from two lintegrals, with the predicate EntropyWellDefined; reason: a Bochner integral would read h = −∞ as 0
--   - encoding: det M → the real part of det M; reason: det M is real on positive definite M
--   - generalization: H_d^{++} defined for d ≥ 1 (§3) → d = 0 allowed, the empty matrix being positive definite with det = 1; reason: the d ≥ 1 statements are a special case; d = 0 is the one-point space (and forces n = 0 where rows are nonzero)
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 3, Eq. (3), p.4

import Mathlib
import Definitions.Def_PsdPermanent_IsProbDensity
import Definitions.Def_PsdPermanent_entropy
import Definitions.Def_PsdPermanent_secondMoment
import Definitions.Def_PsdPermanent_cnDensity
open Matrix
open scoped ComplexOrder

namespace PsdPermanent

/-- **Lemma 3 (Complex entropy bound).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 3 and Eq. (3), p.4: "Let µ be a probability density on C^d with finite second moment, let Z ∼ µ, and
set M = E_µ[ZZ†]. Then M ≻ 0, and h(µ) ≤ d log π + d + log det M, with equality at CN(0, M)."

**Formalization Note.** `h` is `EReal`-valued and may be `−∞`; the statement concludes that it is well-defined. The
equality clause is the entropy of `cnDensity M` for this `M`; `PsdPermanent.cnDensity_facts` has it for every
positive definite matrix, and shows that `M` is the second moment of `cnDensity M`. -/
theorem lemma_3 {d : ℕ} (f : (Fin d → ℂ) → ℝ) (hf : IsProbDensity f) (h2 : FiniteSecondMoment f) :
    (secondMoment f).PosDef ∧ EntropyWellDefined f ∧
      entropy f ≤ (((d : ℝ) * Real.log Real.pi + d + Real.log (secondMoment f).det.re : ℝ) : EReal) ∧
      entropy (cnDensity (secondMoment f)) =
        (((d : ℝ) * Real.log Real.pi + d + Real.log (secondMoment f).det.re : ℝ) : EReal) := by sorry

end PsdPermanent
