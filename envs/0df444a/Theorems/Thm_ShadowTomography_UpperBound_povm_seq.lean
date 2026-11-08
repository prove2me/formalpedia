-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_povm_seq
-- name    : ShadowTomography.UpperBound.povm_seq
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:19.5603+00:00
-- url     : https://prove2.me/theorems/36e8e997-3e29-4042-97c0-2c19de87146b
-- title:
--   Two-stage adaptive measurements on fresh copies
-- statement:
--   Let $a,b\ge0$, let $P$ be a POVM with finite outcome set $\Omega_1$ on $\mathcal H^{\otimes a}$, and for each $\omega_1\in\Omega_1$ let $Q_{\omega_1}$ be a POVM with finite outcome set $\Omega_2$ on $\mathcal H^{\otimes b}$. Then there is a POVM $R$ on $\mathcal H^{\otimes(a+b)}$ with outcomes $\Omega_1\times\Omega_2$, independent of any state, realising "measure $a$ copies with $P$, then $b$ fresh copies with $Q_{\omega_1}$", such that the following holds. For every density operator $\rho$, events $S\subseteq\Omega_1$ and $\mathrm{good}_{\omega_1}\subseteq\Omega_2$, and $\delta_1\in\mathbb R$, $\delta_2\ge0$: if
--   $$
--   \Pr\big[P\text{ on }\rho^{\otimes a}\in S\big]\ge1-\delta_1
--   \quad\text{and}\quad
--   \Pr\big[Q_{\omega_1}\text{ on }\rho^{\otimes b}\in\mathrm{good}_{\omega_1}\big]\ge1-\delta_2\ \ \text{for all }\omega_1\in S,
--   $$
--   then
--   $$
--   \Pr\big[R\text{ on }\rho^{\otimes(a+b)}\text{ yields }(\omega_1,\omega_2)\text{ with }\omega_2\in\mathrm{good}_{\omega_1}\big]\ge1-\delta_1-\delta_2 .
--   $$
--
--   Each round of the shadow-tomography algorithm is such a two-stage measurement: a search over amplified tests followed by a verification of the test found on fresh copies.
--
--   **Formalization Note** The hypothesis $\delta_2\ge0$ is needed when no outcome lies in $S$.
-- source:
--   S. Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, https://arxiv.org/abs/1711.01053, Section 5 (proof of Theorem 2), pp. 15-19

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal
import Definitions.Def_ShadowTomography_UpperBound_seqAccept
set_option autoImplicit false

open scoped ComplexOrder MatrixOrder

namespace ShadowTomography.UpperBound

/-- **K7.** Two-stage adaptive measurement on fresh copies: measure `a` copies with `P`, then
`b` further copies with a POVM `Q ω₁` chosen from the first outcome. There is one POVM on all
`a + b` copies (independent of the state) recording both outcomes such that, if the first stage
lands in `S` with probability `≥ 1 - δ₁` and after every first outcome in `S` the second stage is
good with probability `≥ 1 - δ₂` (`δ₂ ≥ 0`), then the pair is good with probability
`≥ 1 - δ₁ - δ₂`. -/
theorem povm_seq {n : Type} [Fintype n] [DecidableEq n] {Ω₁ Ω₂ : Type} [Fintype Ω₁]
    [Fintype Ω₂] (a b : ℕ) (P : POVM Ω₁ (Fin a → n)) (Q : Ω₁ → POVM Ω₂ (Fin b → n)) :
    ∃ R : POVM (Ω₁ × Ω₂) (Fin (a + b) → n),
      ∀ ρ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ →
        ∀ (S : Ω₁ → Prop) (good : Ω₁ → Ω₂ → Prop) (δ₁ δ₂ : ℝ), 0 ≤ δ₂ →
          1 - δ₁ ≤ P.prob (tensorPow ρ a) S →
          (∀ ω₁, S ω₁ → 1 - δ₂ ≤ (Q ω₁).prob (tensorPow ρ b) (good ω₁)) →
          1 - δ₁ - δ₂ ≤ R.prob (tensorPow ρ (a + b)) (fun ω => good ω.1 ω.2) := by
  sorry

end ShadowTomography.UpperBound
