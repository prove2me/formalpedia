-- Prove2me | Theorems.Thm_SYKCavity_lemma_39
-- name    : SYKCavity.lemma_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:38.449078+00:00
-- url     : https://prove2.me/theorems/5064c7b6-8f03-455d-a618-e38bdc4c3569
-- title:
--   Lemma 39 — concentration of the SYK partition function $Z=\mathrm{Tr}\,e^{\beta H}$: $\log\mathbb EZ-\mathbb E\log Z\le C_\beta/N$, $\Pr[Z<\tfrac12\mathbb EZ]\le C_\beta e^{-N/C_\beta}$
-- statement:
--   Fix $\beta\in\mathbb R$ and let $Z(J)=\operatorname{Tr}e^{\beta H}$ for the SYK Hamiltonian with independent standard Gaussian couplings. There is a constant $C_\beta>0$ such that for every $N\ge1$:
--
--   1. $\mathbb E\,e^{t(\log Z-\mathbb E\log Z)}\le e^{C_\beta t^2/N}$ for every real $t$;
--   2. $0\le\log\mathbb EZ-\mathbb E\log Z\le C_\beta/N$;
--   3. $\mathbb EZ^2/(\mathbb EZ)^2\le e^{C_\beta/N}$;
--   4. $\Pr\bigl[Z<\tfrac12\mathbb EZ\bigr]\le C_\beta e^{-N/C_\beta}$;
--
--   and $Z$, $Z^2$ and $\log Z$ are integrable.
--
--   The algorithm divides by $\mathbb E_J\operatorname{Tr}e^{\beta H}$ instead of $\operatorname{Tr}e^{\beta H}$; part 4 is what makes this harmless with high probability.
--
--   **Formalization Note** $Z$ is the real part of the trace (the trace is real and positive). The moment generating function is a lower Lebesgue integral; the other expectations are Bochner integrals, made meaningful by the integrability clauses.
--
--   Differences from the source:
--   - encoding: the SYK Hamiltonian of Section 3, ψ_i Majoranas with {ψ_i, ψ_j} = 2δ_ij I → H = √(3/(8N³)) Σ_A J_A Γ_A with ψ_i the first N Jordan–Wigner generators on ⌈N/2⌉ qubits, sites Fin N; reason: standard representation (unique up to equivalence for even N); every milestone is a disorder average or uses Section 3's Γ-form as printed
--   - reading: constants C_β (N implicit) → one C_β > 0 for all four bounds and every N ≥ 1; reason: proof p.84: "increase the constants for smaller N"
--   - generalization: the expectations E Z, E Z², E log Z → the conclusion also asserts that Z, Z² and log Z are integrable; reason: it makes the Bochner expectations the page's numbers; true by Gaussian integrability (E.8); it adds to the conclusion and specializes to (B.1)–(B.2)
--   - encoding: Z = Tr e^{βH}; E e^{t(log Z − E log Z)}; Pr → Re Tr e^{βH}; lower Lebesgue integral; the Gaussian measure of {Z < EZ/2}; reason: the trace is real; the integrand is nonnegative
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Lemma 39, p.84, (B.1)–(B.2)

import Mathlib
import Definitions.Def_SYKCavity_Majorana

open MeasureTheory

namespace SYKCavity

/-- **Lemma 39 (Partition-function concentration)**, p.84 of A. Schmidhuber, A. Zlokapa,
*Polynomial-time algorithms for mean-field models up to the glass transition*, arXiv:2610.06807
(held version, sha256 25d817ba…cfc5), (B.1)–(B.2).

For fixed `β`, with `Z(J) = Tr e^{βH}`, there is `C_β` such that for every `N ≥ 1`:
`E e^{t(log Z − E log Z)} ≤ e^{C_β t²/N}` for every real `t`, `0 ≤ log EZ − E log Z ≤ C_β/N`,
`EZ²/(EZ)² ≤ e^{C_β/N}` and `Pr[Z < EZ/2] ≤ C_β e^{−N/C_β}`.

**Formalization Note.** `H` is Section 3's Hamiltonian and `E`, `Pr` are taken under `gaussLaw N`.
`Z(J)` is the real part of the trace (the trace of `e^{βH}`, `H` Hermitian, is real and positive).
The conclusion also asserts that `Z`, `Z²` and `log Z` are integrable, so the expectations are the
page's numbers rather than junk values; the moment generating function is a lower Lebesgue integral.
One constant `C_β > 0` serves all four bounds. -/
theorem lemma_39 (β : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      Integrable (fun J => (expH β N J 1).trace.re) (gaussLaw N) ∧
      Integrable (fun J => (expH β N J 1).trace.re ^ 2) (gaussLaw N) ∧
      Integrable (fun J => Real.log (expH β N J 1).trace.re) (gaussLaw N) ∧
      (∀ t : ℝ,
        ∫⁻ J, ENNReal.ofReal (Real.exp (t * (Real.log (expH β N J 1).trace.re -
            ∫ J', Real.log (expH β N J' 1).trace.re ∂(gaussLaw N)))) ∂(gaussLaw N) ≤
          ENNReal.ofReal (Real.exp (C * t ^ 2 / N))) ∧
      0 ≤ Real.log (∫ J, (expH β N J 1).trace.re ∂(gaussLaw N)) -
          ∫ J, Real.log (expH β N J 1).trace.re ∂(gaussLaw N) ∧
      Real.log (∫ J, (expH β N J 1).trace.re ∂(gaussLaw N)) -
          ∫ J, Real.log (expH β N J 1).trace.re ∂(gaussLaw N) ≤ C / N ∧
      (∫ J, (expH β N J 1).trace.re ^ 2 ∂(gaussLaw N)) /
          (∫ J, (expH β N J 1).trace.re ∂(gaussLaw N)) ^ 2 ≤ Real.exp (C / N) ∧
      gaussLaw N {J | (expH β N J 1).trace.re <
          1 / 2 * ∫ J', (expH β N J' 1).trace.re ∂(gaussLaw N)} ≤
        ENNReal.ofReal (C * Real.exp (-(N : ℝ) / C)) := by sorry

end SYKCavity
