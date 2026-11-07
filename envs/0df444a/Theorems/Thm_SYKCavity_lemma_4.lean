-- Prove2me | Theorems.Thm_SYKCavity_lemma_4
-- name    : SYKCavity.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:53.151044+00:00
-- url     : https://prove2.me/theorems/970f3f8d-f700-474b-93c3-51177c7c3376
-- title:
--   Lemma 4 — Hermite truncation: $\mathbb E_J|\mathrm{Tr}(Oe^{\beta H})/\mathbb E_J\mathrm{Tr}\,e^{\beta H}-\mathcal N_O(J)|^2\le C_{\beta,V,w}N^{-V-1-w/2}$
-- statement:
--   Let $\beta\ge0$, $V$ a truncation order and $w$ a weight. There is $C=C_{\beta,V,w}$ such that for every $N\ge1$ and every observable $O=i^{w(w-1)/2}\psi_{i_1}\cdots\psi_{i_w}$, $i_1<\dots<i_w$,
--   $$\mathbb E_J\Bigl|\frac{\operatorname{Tr}(Oe^{\beta H})}{\mathbb E_J\operatorname{Tr}e^{\beta H}}-\mathcal N_O(J)\Bigr|^2\le C\,N^{-V-1-w/2},\qquad\mathbb E_J\Bigl|\frac{\operatorname{Tr}e^{\beta H}}{\mathbb E_J\operatorname{Tr}e^{\beta H}}-\mathcal N_I(J)\Bigr|^2\le C\,N^{-V-1},\qquad(4.4)$$
--   where $\mathcal N_O$ is the Hermite expansion (4.2) truncated at order $V$ and $\mathcal N_I$ is $\mathcal N_O$ at $O=I$.
--
--   The algorithm evaluates $\mathcal N_O(J)/\mathcal N_I(J)$; this lemma bounds the error of truncating the Hermite expansion at order $V$.
--
--   **Formalization Note** $H$ is Section 3's form. The outer expectations are lower Lebesgue integrals of $|\cdot|^2$; $N^{-V-1-w/2}$ is a real power.
--
--   Differences from the source:
--   - encoding: the SYK Hamiltonian of Section 3, ψ_i Majoranas with {ψ_i, ψ_j} = 2δ_ij I → H = √(3/(8N³)) Σ_A J_A Γ_A with ψ_i the first N Jordan–Wigner generators on ⌈N/2⌉ qubits, sites Fin N; reason: standard representation (unique up to equivalence for even N); every milestone is a disorder average or uses Section 3's Γ-form as printed
--   - reading: C_{β,V,w}, C_{β,V}; O the observable of Theorem 2 → one C (after β, V, w) for every N ≥ 1 and every weight-w observable; the second bound is independent of w and O; reason: Lemma 4 is applied to the O of Theorem 2 for all N; the second display does not involve w
--   - encoding: E_J|·|² → lower Lebesgue integral of ‖·‖ₑ² (complex values); reason: nonnegative integrand; avoids the Bochner junk value
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Lemma 4, p.26, (4.4); (4.1)–(4.2), p.25

import Mathlib
import Definitions.Def_SYKCavity_Hermite

open MeasureTheory

namespace SYKCavity

/-- **Lemma 4 (Hermite truncation)**, p.26 of A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms
for mean-field models up to the glass transition*, arXiv:2610.06807 (held version, sha256
25d817ba…cfc5), (4.4).

For `β ≥ 0` and truncation order `V`, for every weight `w` there is `C_{β,V,w}` such that for every
`N ≥ 1` and every `O = i^{w(w−1)/2} ψ_{i_1} ⋯ ψ_{i_w}`, `i_1 < ⋯ < i_w`:
`E_J |Tr(O e^{βH}) / E_J Tr e^{βH} − N_O(J)|² ≤ C_{β,V,w} N^{−V−1−w/2}` and
`E_J |Tr e^{βH} / E_J Tr e^{βH} − N_I(J)|² ≤ C_{β,V} N^{−V−1}`.

**Formalization Note.** `H` is Section 3's Hamiltonian; `N_O` is (4.2) (`NO`), and `N_I` is `N_O` at
`O = I`. The outer expectations are lower Lebesgue integrals of `‖·‖²`; `N^{−V−1−w/2}` is a real
power. -/
theorem lemma_4 (β : ℝ) (hβ : 0 ≤ β) (V w : ℕ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ idx : Fin w ↪o Fin N,
      (∫⁻ J, ‖(obs N idx * expH β N J 1).trace / (∫ J', (expH β N J' 1).trace ∂(gaussLaw N)) -
          NO β V N (obs N idx) J‖ₑ ^ 2 ∂(gaussLaw N) ≤
        ENNReal.ofReal (C * (N : ℝ) ^ (-(V : ℝ) - 1 - (w : ℝ) / 2))) ∧
      (∫⁻ J, ‖(expH β N J 1).trace / (∫ J', (expH β N J' 1).trace ∂(gaussLaw N)) -
          NO β V N 1 J‖ₑ ^ 2 ∂(gaussLaw N) ≤
        ENNReal.ofReal (C * (N : ℝ) ^ (-(V : ℝ) - 1))) := by sorry

end SYKCavity
