-- Prove2me | Theorems.Thm_PsdPermanent_gibbs_admissible
-- name    : PsdPermanent.gibbs_admissible
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:19.136877+00:00
-- url     : https://prove2.me/theorems/afd4f422-84f6-4cdf-951d-38d8205597b6
-- title:
--   Proof of Theorem 7, p.7 — the Gibbs density of the permanent is admissible
-- statement:
--   Let $V\in\mathbb C^{n\times d}$ have nonzero rows, and let $U(z)=\sum_i\log|v_i^\dagger z|^2$. Then $U$ is measurable, never $+\infty$, and
--   $$Z_U=\pi^{-d}\int_{\mathbb C^d}\exp(U(z)-z^\dagger z)\,dz=\mathrm{per}(VV^\dagger),$$
--   with $Z_U$ finite and positive. The Gibbs density proportional to $\exp(U(z)-z^\dagger z)$ has finite second moment, finite entropy and finite $\mathbb E[U(Z)]$; in particular it is admissible.
--
--   This is the condition under which the Gibbs formula applies to the permanent.
--
--   Differences from the source:
--   - encoding: finite entropy and finite E[U(Z)] → both parts of each of the two extended real numbers are finite; reason: each is a difference of its two parts
--   - encoding: log per(A) = log[π^{−d} ∫ exp(U(z) − z†z) dz] → Z_U = ofReal (Re per(V V†)) in [0, ∞]; reason: the logarithms of equal numbers; Lemma 6 gives that per is real
--   - generalization: V the full column rank Gram factor of §3, as in the proof of Theorem 7 → any V with nonzero rows; reason: finiteness and positivity of Z_U and the moments of the Gibbs density use only v_i ≠ 0; full column rank factors are a special case
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), proof of Theorem 7, p.7

import Mathlib
import Definitions.Def_PsdPermanent_secondMoment
import Definitions.Def_PsdPermanent_entropy
import Definitions.Def_PsdPermanent_gibbsDensity
import Definitions.Def_PsdPermanent_Admissible
import Definitions.Def_PsdPermanent_logProductPotential
open Matrix

namespace PsdPermanent

/-- **The Gibbs density of the permanent is admissible.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), proof of Theorem 7, p.7: "Let U(z) = ∑_{i=1}^n log|v_i† z|². By Lemma 6, log per(A) = log[π^{−d} ∫_{C^d} exp(U(z) − z†z)
dz]. The integral is finite because the integrand is a polynomial times a Gaussian density. It is positive because the zero
set of ∏_i v_i† z is a finite union of proper complex hyperplanes, hence has Lebesgue measure zero. The corresponding Gibbs
density is proportional to a polynomial times the standard Gaussian density, so it has finite second moment, finite
entropy, and finite E[U(Z)]. Thus Lemma 4 applies."

**Formalization Note.** Nonzero rows, as in the proof. The hypotheses of `PsdPermanent.lemma_4` are all concluded here, plus
finiteness of the four parts of `h` and `E[U]`, and `Z_U = per(A)` (the display, in `[0, ∞]`). -/
theorem gibbs_admissible {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) (hV : ∀ i, V i ≠ 0) :
    Measurable (logProductPotential V) ∧ (∀ z, logProductPotential V z ≠ ⊤) ∧
      partitionZ (logProductPotential V) = ENNReal.ofReal (V * Vᴴ).permanent.re ∧
      partitionZ (logProductPotential V) ≠ 0 ∧ partitionZ (logProductPotential V) ≠ ⊤ ∧
      Admissible (logProductPotential V) (gibbsDensity (logProductPotential V)) ∧
      entropyPos (gibbsDensity (logProductPotential V)) ≠ ⊤ ∧
      entropyNeg (gibbsDensity (logProductPotential V)) ≠ ⊤ ∧
      expectationPos (logProductPotential V) (gibbsDensity (logProductPotential V)) ≠ ⊤ ∧
      expectationNeg (logProductPotential V) (gibbsDensity (logProductPotential V)) ≠ ⊤ := by sorry

end PsdPermanent
