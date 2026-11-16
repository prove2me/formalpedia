-- Prove2me | Theorems.Thm_SpectrumLB_Supplement_theorem_4_4
-- name    : SpectrumLB.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:01:14.847187+00:00
-- url     : https://prove2.me/theorems/fc251257-e5b8-4ff9-b256-b2774e2254e4
-- title:
--   Theorem 4.4 — $D(\overline\rho^{(n)}_{\mathrm{proj}}\,\|\,\overline\rho^{(n)}_{\mathrm{Haar}})\le Cn^3/d^4$ for even $d$ and $1\le n\le d^2$
-- statement:
--   Let $\overline\rho^{(n)}_{\mathrm{proj}}=\mathbf E[\rho_{\mathrm{proj}}^{\otimes n}]$ with $\rho_{\mathrm{proj}}=\frac2d\Pi$ for a Haar-random rank-$d/2$ projection $\Pi$ on $\mathbb C^d$, and $\overline\rho^{(n)}_{\mathrm{Haar}}=\mathbf E[\rho_{\mathrm{Haar}}^{\otimes n}]$ with $\rho_{\mathrm{Haar}}=\mathrm{Tr}_2[|\psi\rangle\langle\psi|]$ for a Haar-random unit vector $|\psi\rangle\in\mathbb C^d\otimes\mathbb C^d$. Let $D(\rho\|\sigma)=\mathrm{Tr}[\rho(\ln\rho-\ln\sigma)]$ be the quantum relative entropy, equal to $+\infty$ when the support of $\rho$ is not contained in that of $\sigma$. There is a constant $C>0$ such that for every even $d$ and every $n$ with $1\le n\le d^2$,
--
--   $$
--   D\big(\overline\rho^{(n)}_{\mathrm{proj}}\,\big\|\,\overline\rho^{(n)}_{\mathrm{Haar}}\big)\ \le\ C\,\frac{n^3}{d^4}.
--   $$
--
--   By Pinsker's inequality the two ensembles are indistinguishable from $n=o(d^{4/3})$ copies, which is the warm-up $\Omega(d^{4/3})$ lower bound of §4 for spectrum estimation, entropy estimation and rank testing.
--
--   **Formalization Note** $D$ is the platform's `MomentPolytopes.QuantumFunctionals.relEntropy` (natural logarithm, valued in the extended reals, $+\infty$ off support), so the bound includes the support containment. Both average states are defined from Haar measures; $|\psi\rangle$ is a column $Ve_c$ of a Haar unitary on $\mathbb C^{d^2}$ and the statement holds for every column index $c$.
--
--   Differences from the source:
--   - encoding: a Haar-random unit vector |ψ⟩ of ℂ^d ⊗ ℂ^d → the column V e_c of V ∼ Haar on U(d²) (Fin (d*d) via finProdFinEquiv), the bound required for every c; reason: every column of a Haar unitary is uniform on the unit sphere, so haarAvg d n c is the same state for every c and the statement is the paper's
--   - encoding: D(ρ‖σ) = Tr[ρ(log ρ − log σ)], restricted to the support (p.18) → MomentPolytopes.QuantumFunctionals.relEntropy: natural log, EReal-valued, ⊤ if im ρ ⊄ im σ or an argument is not PSD; reason: standard relative entropy; the natural log is the paper's (S uses ln, and (4.30) holds in nats); both averages are PSD
--   - encoding: E[ρ^{⊗n}] for the random states of (4.1), (4.2) → entrywise Bochner expectation (WildeQIT.Covering.expectation) of piKron n over the Haar measure; reason: the entries are continuous on a compact group, hence integrable; same matrix
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Theorem 4.4, Eq. (4.28), p. 18 (objects: Eqs. (4.1), (4.2), p. 15; (4.16), (4.18), p. 17)

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_RelativeEntropy
import Definitions.Def_SpectrumLB_Supplement_projAvg
import Definitions.Def_SpectrumLB_Supplement_haarAvg

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB.Supplement

/-- **Theorem 4.4 (relative entropy of the warm-up average states).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680,
Theorem 4.4, Eq. (4.28), p. 18: "There exists a constant C > 0 such that for any even d and
1 ≤ n ≤ d^2, D(ρ̄^{(n)}_proj ‖ ρ̄^{(n)}_Haar) ≤ C n^3/d^4."

There is one constant `C > 0` such that for every even `d`, every `n` with `1 ≤ n ≤ d²` (and every
choice of the column `c` realizing the Haar vector `|ψ⟩ = V e_c`),
`D(E[ρ_proj^{⊗n}] ‖ E[ρ_Haar^{⊗n}]) ≤ C · n³ / d⁴`.

**Formalization Note.** `D` is the platform's `MomentPolytopes.QuantumFunctionals.relEntropy`:
`Tr[A log A] − Tr[A log B]` with the natural logarithm, valued in `EReal`, and `+∞` when
`im A ⊄ im B` (or an argument is not positive semidefinite), so the bound includes the support
condition. The averages are `projAvg` (Eqs. (4.1), (4.16)) and `haarAvg` (Eqs. (4.2), (4.18)),
built from Haar measures, not from the Jucys–Murphy closed forms. `haarAvg` does not depend on
`c`; quantifying over every `c` is the paper's statement. `C` is chosen before `d` and `n`. -/
theorem theorem_4_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, Even d → ∀ n : ℕ, 1 ≤ n → n ≤ d ^ 2 → ∀ c : Fin (d * d),
      MomentPolytopes.QuantumFunctionals.relEntropy (projAvg d n) (haarAvg d n c) ≤
        ((C * (n : ℝ) ^ 3 / (d : ℝ) ^ 4 : ℝ) : EReal) := by sorry

end SpectrumLB.Supplement
