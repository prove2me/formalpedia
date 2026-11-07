-- Prove2me | Theorems.Thm_SYKCavity_corollary_6
-- name    : SYKCavity.corollary_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:37.806899+00:00
-- url     : https://prove2.me/theorems/99650ecb-90e3-436a-8ec6-00a1ffb164a3
-- title:
--   Corollary 6 — concentration of the centered moments: $\|\mu_p\|_\infty\le C_{\beta,p}N^{-\theta p}$
-- statement:
--   For every constant $\beta\ge0$ there is $\theta>0$ such that for every constant $p\ge1$ there is $C_{\beta,p}$ with
--   $$\|\mu_p\|_\infty\le C_{\beta,p}N^{-\theta p}\qquad(4.15)$$
--   for every $N\ge1$, where $\|\cdot\|_\infty$ is the supremum over all times $(u_r,v_r)\in[0,1]^2$ and over every coincident-time prescription of Lemma 42 (each ordered limit and the alternating value).
--
--   Concentration lets the hierarchy for $\mu_p$ be truncated at a finite order $K$ with error $O(N^{-\theta K})$.
--
--   **Formalization Note** The ordered limits use offsets distinct on the $2p$ occurrences (`muOrd`); `muAlt` is the page's $\mu_p$.
--
--   Differences from the source:
--   - encoding: the SYK Hamiltonian of Section 3, ψ_i Majoranas with {ψ_i, ψ_j} = 2δ_ij I → H = √(3/(8N³)) Σ_A J_A Γ_A with ψ_i the first N Jordan–Wigner generators on ⌈N/2⌉ qubits, sites Fin N; reason: standard representation (unique up to equivalence for even N); every milestone is a disorder average or uses Section 3's Γ-form as printed
--   - encoding: ⟨·⟩_N as the Grassmann ratio (3.19) → the trace-side expression (3.20) with Lemma 42's prescriptions (E.1)–(E.4), as the definition; reason: the page proves the two agree (3.20, Lemma 42); planning decision recorded for the moderator
--   - reading: ‖μ_p‖∞ → the bound at every point of [0,1]^{2p}, for the alternating value and for every ordered limit; reason: the uniform norm (E.11) is the maximum over domains and prescriptions of the supremum over times
--   - reading: C_{β,p} (N implicit) → for every N ≥ 1; reason: constants absorb finitely many N
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Corollary 6, p.28, (4.15); norm (E.11), p.96

import Mathlib
import Definitions.Def_SYKCavity_Correlator

open MeasureTheory

namespace SYKCavity

/-- **Corollary 6 (Concentration of `μ_p`)**, p.28 of A. Schmidhuber, A. Zlokapa, *Polynomial-time
algorithms for mean-field models up to the glass transition*, arXiv:2610.06807 (held version, sha256
25d817ba…cfc5), (4.15).

For every `β ≥ 0` there is `θ > 0` such that for every `p ≥ 1` there is `C_{β,p}` with
`‖μ_p‖∞ ≤ C_{β,p} N^{−θp}` for every `N ≥ 1`.

**Formalization Note.** `‖μ_p‖∞` is the uniform norm of (E.11): the supremum over all times
`(u_r, v_r) ∈ [0,1]²` and over every coincident-time prescription of Lemma 42. The statement bounds
every ordered limit (`muOrd`, offsets distinct on the `2p` occurrences) and the alternating value
(`muAlt`, the page's `μ_p`) at every point. -/
theorem corollary_6 (β : ℝ) (hβ : 0 ≤ β) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ p : ℕ, 1 ≤ p → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∀ u v : Fin p → ℝ, (∀ r, u r ∈ Set.Icc (0 : ℝ) 1) → (∀ r, v r ∈ Set.Icc (0 : ℝ) 1) →
        ‖muAlt β N p u v‖ ≤ C * (N : ℝ) ^ (-(θ * p)) ∧
        ∀ ηu ηv : Fin p → ℝ, Function.Injective (pairList ηu ηv) →
          ‖muOrd β N p u v ηu ηv‖ ≤ C * (N : ℝ) ^ (-(θ * p)) := by sorry

end SYKCavity
