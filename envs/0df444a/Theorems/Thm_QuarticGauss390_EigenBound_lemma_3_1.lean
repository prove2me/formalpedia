-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_lemma_3_1
-- name    : QuarticGauss390.EigenBound.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:25.680942+00:00
-- url     : https://prove2.me/theorems/15876a69-ba0a-4d05-b625-759e318fa92a
-- title:
--   Lemma 3.1 — the maximal-overlap Gaussian: $\langle\xi|Q_x|g\rangle=0$ and $|\langle\xi|Q_x^2|g\rangle|\le a\,\mathrm{Var}_g(Q_x)\le 2a\|x\|^2$
-- statement:
--   Fix a CAR system on $n\ge2$ modes and a state $|\psi\rangle$ (a unit vector).
--
--   1. Some pure Gaussian state $|g\rangle$ maximizes $|\langle g|\psi\rangle|$ over all Gaussian states, and the maximum is positive.
--   2. Let $|g\rangle$ be such a maximizer whose overlap $a:=\langle g|\psi\rangle$ is real and positive, and let $|\xi\rangle=|\psi\rangle-a|g\rangle$. Then for every $x\in\mathbb R^E$,
--   $$\langle\xi|Q_x|g\rangle=0,\qquad |\langle\xi|Q_x^2|g\rangle|\le a\operatorname{Var}_g(Q_x)\le 2a\|x\|^2,$$
--   and
--   $$\left|\frac{\langle g|Q_x^2|\psi\rangle}{a}-\langle Q_x^2\rangle_g\right|\le\operatorname{Var}_g(Q_x)\le 2\|x\|^2 .$$
--
--   The lemma says that projecting a state onto its closest Gaussian direction leaves a residual that is invisible to quadratic Hamiltonians and almost invisible to their squares; it is the main technical lemma behind Lemma 3.2.
--
--   Differences from the source:
--   - encoding: "let $|g\rangle$ be a Gaussian maximizing $|\langle g|\psi\rangle|$ … the maximum is positive … choose the phase so that $a>0$" → clause 1 asserts that a maximizer exists and the maximum is positive; clause 2 assumes a maximizer with $\langle g|\psi\rangle=a$ real and $a>0$; reason: these are the lemma's own assertions and setup; a unit-modulus multiple of a Gaussian is Gaussian with the same $O$, so every maximizer can be rephased
--   - encoding: $\operatorname{Var}_g$, $\|x\|^2$, $\langle Q_x^2\rangle_g$ → real part of $\langle g|(Q_x-\langle Q_x\rangle_gI)^2|g\rangle$, $\sum_px_p^2$, $\langle g|Q_x^2|g\rangle$; reason: same quantities
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.10, Lemma 3.1, eq. (3.1)–(3.2)

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Gaussian
import Definitions.Def_QuarticGauss390_EigenBound_Moments

open Matrix

namespace QuarticGauss390.EigenBound

/-- Lemma 3.1, p.10: (i) for a state `|ψ⟩` some Gaussian maximizes `|⟨g|ψ⟩|` and the maximum
is positive; (ii) if `|g⟩` is such a maximizer with `a := ⟨g|ψ⟩ > 0` and
`|ξ⟩ = |ψ⟩ - a|g⟩`, then for every `x`: `⟨ξ|Q_x|g⟩ = 0`,
`|⟨ξ|Q_x²|g⟩| ≤ a Var_g(Q_x) ≤ 2a‖x‖²` (3.1), and
`|⟨g|Q_x²|ψ⟩/a - ⟨Q_x²⟩_g| ≤ Var_g(Q_x) ≤ 2‖x‖²` (3.2). -/
theorem lemma_3_1 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) (ψ : Vec n) (hψ : IsState ψ) :
    (∃ g : Vec n, IsGaussian C g ∧
      (∀ g' : Vec n, IsGaussian C g' → ‖star g' ⬝ᵥ ψ‖ ≤ ‖star g ⬝ᵥ ψ‖) ∧
      0 < ‖star g ⬝ᵥ ψ‖) ∧
    (∀ g : Vec n, IsGaussian C g →
      (∀ g' : Vec n, IsGaussian C g' → ‖star g' ⬝ᵥ ψ‖ ≤ ‖star g ⬝ᵥ ψ‖) →
      ∀ a : ℝ, star g ⬝ᵥ ψ = (a : ℂ) → 0 < a →
      ∀ x : Pair n → ℝ,
        let ξ : Vec n := ψ - (a : ℂ) • g
        let Q : Op n := quadHam C x
        star ξ ⬝ᵥ (Q *ᵥ g) = 0 ∧
        ‖star ξ ⬝ᵥ ((Q * Q) *ᵥ g)‖ ≤ a * variance (pureProj g) Q ∧
        a * variance (pureProj g) Q ≤ 2 * a * ∑ p, x p ^ 2 ∧
        ‖star g ⬝ᵥ ((Q * Q) *ᵥ ψ) / (a : ℂ) - star g ⬝ᵥ ((Q * Q) *ᵥ g)‖ ≤
          variance (pureProj g) Q ∧
        variance (pureProj g) Q ≤ 2 * ∑ p, x p ^ 2) := by sorry

end QuarticGauss390.EigenBound
