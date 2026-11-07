-- Prove2me | Theorems.Thm_PsdPermanent_cnDensity_facts
-- name    : PsdPermanent.cnDensity_facts
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:22.57338+00:00
-- url     : https://prove2.me/theorems/61a5e415-8e65-4fe6-91fc-41e71d0f877d
-- title:
--   §3, p.3 — $\mathcal{CN}(0,X)$: density, second moment, entropy
-- statement:
--   Let $X$ be a Hermitian positive definite $d\times d$ matrix. The function
--   $$z\mapsto\frac{1}{\pi^d\det X}\exp(-z^\dagger X^{-1}z)$$
--   is a probability density on $\mathbb C^d$ with finite second moment and second moment $\mathbb E[ZZ^\dagger]=X$. Its differential entropy is well-defined and equals
--   $$h(Z)=d\log\pi+d+\log\det X.$$
--
--   These are the facts about the Gaussian trial density used in the lower bound of Theorem 7.
--
--   Differences from the source:
--   - encoding: h, a real number or ±∞ when well-defined → an EReal built from two lintegrals, with the predicate EntropyWellDefined; reason: a Bochner integral would read h = −∞ as 0
--   - encoding: Z ∼ CN(0, X) has that density, and E[Z†Z] = trX in the proof of Theorem 7 → the formula is concluded to be a probability density with finite second moment and second moment X; reason: this is what the notation asserts, and trace X = E[Z†Z] follows
--   - generalization: H_d^{++} defined for d ≥ 1 (§3) → d = 0 allowed, the empty matrix being positive definite with det = 1; reason: the d ≥ 1 statements are a special case; d = 0 is the one-point space (and forces n = 0 where rows are nonzero)
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3

import Mathlib
import Definitions.Def_PsdPermanent_IsProbDensity
import Definitions.Def_PsdPermanent_entropy
import Definitions.Def_PsdPermanent_secondMoment
import Definitions.Def_PsdPermanent_cnDensity
open Matrix
open scoped ComplexOrder

namespace PsdPermanent

/-- **The complex Gaussian: density, second moment and entropy.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3: "Z ∼ CN(0, X), for X ∈ H_d^{++}, has density (1 / (π^d det X)) exp(−z† X^{−1} z). Its differential
entropy is h(Z) = d log π + d + log det X."

**Formalization Note.** That the formula is a probability density with finite second moment and second moment `X`
is what "Z ∼ CN(0, X)" means, and the proof of Theorem 7 (p.8) uses it as "E[Z†Z] = trX". -/
theorem cnDensity_facts {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosDef) :
    IsProbDensity (cnDensity X) ∧ FiniteSecondMoment (cnDensity X) ∧ secondMoment (cnDensity X) = X ∧
      EntropyWellDefined (cnDensity X) ∧
      entropy (cnDensity X) = (((d : ℝ) * Real.log Real.pi + d + Real.log X.det.re : ℝ) : EReal) := by sorry

end PsdPermanent
