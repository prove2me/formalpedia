-- Prove2me | Theorems.Thm_SYKCavity_theorem_9
-- name    : SYKCavity.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:59.301271+00:00
-- url     : https://prove2.me/theorems/43645cdb-1eff-4ed0-a7d6-0bb4c35a3958
-- title:
--   Theorem 9 — concentration around the saddle: $\mathbb E_J\mathrm{Tr}(e^{\beta H}B^{2m})/\mathbb E_J\mathrm{Tr}\,e^{\beta H}\le C_mN^{-\delta m/(4r+4)}$
-- statement:
--   Let $\beta\ge0$ and let $B$ be a Hermitian linear combination of finitely many operators
--   $$B(t)=\frac1{2N}\sum_{i=1}^Ne^{-it\beta H}\psi_ie^{it\beta H}\psi_i-G_*(it)I\qquad(5.1)$$
--   at fixed real times, together with their adjoints. There exist $\delta>0$ and an integer $r\ge1$ such that for every integer $m\ge1$ there is $C_m$ with
--   $$\frac{\mathbb E_J\operatorname{Tr}(e^{\beta H}B^{2m})}{\mathbb E_J\operatorname{Tr}e^{\beta H}}\le C_mN^{-\delta m/(4r+4)}\qquad(5.2)$$
--   for every $N\ge1$.
--
--   This is the cavity-method concentration of the empirical two-point function around the saddle $G_*$; Corollary 6 follows from it.
--
--   **Formalization Note** $B=\sum_l(c_lB(t_l)+\bar c_lB(t_l)^\dagger)$ with fixed times and coefficients; the left side is real and nonnegative and is bounded in modulus.
--
--   Differences from the source:
--   - encoding: the SYK Hamiltonian of Section 3, ψ_i Majoranas with {ψ_i, ψ_j} = 2δ_ij I → H = √(3/(8N³)) Σ_A J_A Γ_A with ψ_i the first N Jordan–Wigner generators on ⌈N/2⌉ qubits, sites Fin N; reason: standard representation (unique up to equivalence for even N); every milestone is a disorder average or uses Section 3's Γ-form as printed
--   - encoding: a Hermitian linear combination of finitely many B(t) at fixed real times, together with their adjoints → B = Σ_{l<L} (c_l B(t_l) + c̄_l B(t_l)†) for fixed L, t : Fin L → ℝ, c : Fin L → ℂ; reason: B = (B + B†)/2 puts every Hermitian combination in this form
--   - reading: C_m (N implicit) → for every N ≥ 1; reason: constants absorb finitely many N; the theorem has no "large N"
--   - encoding: the ratio in (5.2) → its complex modulus; reason: the ratio is real and nonnegative
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Theorem 9, pp.31 and 33, (5.1)–(5.2)

import Mathlib
import Definitions.Def_SYKCavity_Correlator
import Definitions.Def_SYKCavity_Bop

open MeasureTheory

namespace SYKCavity

/-- **Theorem 9 (Concentration around saddle solution)**, pp.31 and 33 of A. Schmidhuber,
A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass transition*,
arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (5.1)–(5.2).

Let `β ≥ 0` and let `B` be a Hermitian linear combination of finitely many operators
`B(t) = (1/(2N)) Σ_i e^{−itβH} ψ_i e^{itβH} ψ_i − G*(it) I` at fixed real times, together with their
adjoints. There exist `δ > 0` and an integer `r ≥ 1` such that for every integer `m ≥ 1` there is
`C_m` with `E_J Tr(e^{βH} B^{2m}) / E_J Tr e^{βH} ≤ C_m N^{−δm/(4r+4)}` for every `N ≥ 1`.

**Formalization Note.** `B = Σ_l (c_l B(t_l) + c̄_l B(t_l)†)` with fixed times `t_l` and fixed complex
coefficients `c_l` (independent of `N`); every Hermitian combination has this form. `H` is Section 3's
Hamiltonian; the ratio of disorder averages is `avgRatio` and is bounded in modulus (it is real and
nonnegative). `δ, r` may depend on `β` and `B`; `C_m` also on `m`. -/
theorem theorem_9 (β : ℝ) (hβ : 0 ≤ β) (L : ℕ) (t : Fin L → ℝ) (c : Fin L → ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ r : ℕ, 1 ≤ r ∧ ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ‖avgRatio β N (fun J => expH β N J 1 * Bcomb β N J t c ^ (2 * m))‖ ≤
        C * (N : ℝ) ^ (-(δ * m / (4 * r + 4))) := by sorry

end SYKCavity
