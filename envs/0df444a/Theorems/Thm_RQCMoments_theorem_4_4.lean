-- Prove2me | Theorems.Thm_RQCMoments_theorem_4_4
-- name    : RQCMoments.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:33.215844+00:00
-- url     : https://prove2.me/theorems/23182d8b-e4a2-4cbe-8fd8-7860eb95b98f
-- title:
--   Theorem 4.4 — Gauss weights of $\mathrm{Beta}(1,D)$: $\max_i w_i\le C\sqrt{D/(\ell(\ell+D))}$
-- statement:
--   Let $D\ge 1$ be a real number and $\mu_D=\mathrm{Beta}(1,D)$, $d\mu_D(x)=D(1-x)^{D-1}dx$ on $(0,1)$. Let $x_1<\dots<x_\ell$ and $w_1,\dots,w_\ell$ be the nodes and (positive) weights of the $\ell$-node Gaussian quadrature rule for $\mu_D$, where $\ell\ge 1$, so that the rule is exact for every polynomial of degree at most $2\ell-1$. There is an absolute constant $C>0$ such that
--   $$
--   \max_{1\le i\le\ell}w_i\le C\sqrt{\frac{D}{\ell(\ell+D)}} .
--   $$
--   In particular the constant is uniform when $D$ and $\ell$ grow together.
--
--   With $D=N-1$ and $\ell=k+1$ this gives the rate $\sqrt{N/(k(k+N))}$ of Theorem 4.9.
--
--   Differences from the source:
--
--   - generalization: the ℓ-node Gaussian quadrature rule for μ_D (nodes the zeros of q_ℓ, positive weights) → every rule satisfying IsGaussRule (betaMeasure 1 D) ℓ x w; reason: the Gauss rule is unique and positivity of its weights is a consequence (Lemma 4.1), not an assumption; the source's rule is an instance
--   - reading: D ≥ 1 (§4.1 introduces μ_{a,D} for integers a, D ≥ 1) → every real D ≥ 1; reason: the theorem says only "Let D ≥ 1" while it calls ℓ an integer, and its proof ((82), (84) with the separate case D = 1, (86), (89)) never uses integrality; the integer reading would be the weaker one, and integer D is the special case
--   - encoding: max_{1≤i≤ℓ} w_i ≤ C √(D/(ℓ(ℓ+D))) → ∃ C > 0 (before D, ℓ, the rule), ∀ i, w i ≤ C √(D/(ℓ(ℓ+D))); reason: a bound on the maximum is a bound for every i; the absolute constant comes first
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 4.4, (77)–(78), p.25 (PDF p.27)

import Mathlib
import Definitions.Def_RQCMoments_IsGaussRule

set_option autoImplicit false

namespace RQCMoments

/-- **Theorem 4.4** (uniform upper bound on quadrature weights) (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 4.4, p.25,
PDF p.27).
Let `D ≥ 1` and let `x₁ < ⋯ < x_ℓ`, `w₁, …, w_ℓ` be the nodes and weights of the `ℓ`-node Gaussian
quadrature rule for `μ_D = Beta(1, D)`, `dμ_D(x) = D(1−x)^{D−1} dx` on `(0,1)` (77), where `ℓ ≥ 1`.
There is an absolute constant `C > 0` such that `max_i wᵢ ≤ C √(D/(ℓ(ℓ+D)))` (78).

**Formalization Note** `D` is any real number `≥ 1`: the theorem says "Let `D ≥ 1`" while it
calls `ℓ` an integer, and its proof (Steps 1–2, (82) and (84), including the separate case
`D = 1`) never uses integrality; integer `D` (§4.1, and `D = N − 1` in Theorem 4.9) is the special
case. `μ_D` is Mathlib's `betaMeasure 1 D`. The Gauss rule is any rule satisfying `IsGaussRule` (unique). `C` is
chosen before `D`, `ℓ` and the rule. -/
theorem theorem_4_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 1 ≤ D → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ x w : Fin ℓ → ℝ,
      IsGaussRule (ProbabilityTheory.betaMeasure 1 D) ℓ x w →
        ∀ i, w i ≤ C * Real.sqrt (D / ((ℓ : ℝ) * ((ℓ : ℝ) + D))) := by sorry

end RQCMoments
