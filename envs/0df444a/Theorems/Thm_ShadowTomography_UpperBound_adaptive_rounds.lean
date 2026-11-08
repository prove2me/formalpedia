-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_adaptive_rounds
-- name    : ShadowTomography.UpperBound.adaptive_rounds
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:18.559888+00:00
-- url     : https://prove2.me/theorems/7ebf60c2-5cef-45ea-aa74-71479ce2b077
-- title:
--   Adaptive rounds on fresh blocks of copies: a union bound
-- statement:
--   Let $R,k\ge0$ and let $\Omega$ be a finite set of outcomes. Suppose that for every round $r<R$ and every history $h\in\Omega^{r}$ of previous outcomes we are given a POVM $P_{r,h}$ with outcomes in $\Omega$ acting on $k$ copies, $\mathcal H^{\otimes k}$. Then there is a single POVM $Q$ on $\mathcal H^{\otimes Rk}$ with outcomes in $\Omega^R$, not depending on any state, which realises the adaptive procedure "in round $r$, measure a fresh block of $k$ copies with $P_{r,h}$, where $h$ is the record so far", in the following sense. For every density operator $\rho$, every family of events $\mathrm{good}_{r,h}\subseteq\Omega$ and every $\delta_0,\dots,\delta_{R-1}$: if
--   $$
--   \Pr\big[P_{r,h}\text{ on }\rho^{\otimes k}\text{ lands in }\mathrm{good}_{r,h}\big]\ge1-\delta_r\quad\text{for all } r,h,
--   $$
--   then
--   $$
--   \Pr\big[Q\text{ on }\rho^{\otimes Rk}\text{ yields }\omega\text{ with }\omega_r\in\mathrm{good}_{r,\omega_{<r}}\text{ for all }r\big]\ge 1-\sum_{r<R}\delta_r .
--   $$
--
--   The shadow-tomography algorithm consumes fresh copies in each of its $T$ rounds (p. 16, "assume ... fresh copies"); this lemma turns the per-round guarantees into a guarantee for the whole procedure.
--
--   **Formalization Note** The $k$-copy blocks are laid out consecutively in $\mathrm{Fin}(Rk)$; the history of round $r$ is the restriction of the record to the first $r$ rounds.
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

/-- **K3.** Adaptive rounds on fresh blocks of i.i.d. copies. For `R` rounds, each measuring a
fresh block of `k` copies with a POVM chosen from the previous outcomes, there is a single POVM
on all `R k` copies (independent of the state), whose outcome is the record of all rounds, such
that: if in every round and after every history the "good" event has probability at least
`1 - δ_r`, then all rounds are good with probability at least `1 - ∑_r δ_r`. -/
theorem adaptive_rounds {n : Type} [Fintype n] [DecidableEq n] {Ω : Type} [Fintype Ω]
    (R k : ℕ) (P : ∀ r : Fin R, (Fin r → Ω) → POVM Ω (Fin k → n)) :
    ∃ Q : POVM (Fin R → Ω) (Fin (R * k) → n),
      ∀ (ρ : Matrix n n ℂ), WildeQIT.IsDensityOperator ρ →
        ∀ (good : ∀ r : Fin R, (Fin r → Ω) → Ω → Prop) (δ : Fin R → ℝ),
          (∀ r h, 1 - δ r ≤ (P r h).prob (tensorPow ρ k) (good r h)) →
          1 - ∑ r, δ r ≤ Q.prob (tensorPow ρ (R * k))
            (fun ω => ∀ r : Fin R,
              good r (fun i => ω (Fin.castLT i (lt_trans i.isLt r.isLt))) (ω r)) := by
  sorry

end ShadowTomography.UpperBound
