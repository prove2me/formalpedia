-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_povm_lift
-- name    : ShadowTomography.UpperBound.povm_lift
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:28.918604+00:00
-- url     : https://prove2.me/theorems/64334806-bc77-4348-af83-de2c3b4e0a23
-- title:
--   Running a block measurement on more copies than needed
-- statement:
--   Let $q,k,\ell\ge0$ with $k\le\ell$, and let $P=(P_\omega)_{\omega\in\Omega}$ be a POVM on $(\mathcal H^{\otimes q})^{\otimes k}$, i.e. a measurement of $k$ blocks of $q$ registers each. Then there is a POVM $P'$ on $\mathcal H^{\otimes q\ell}$ with the same outcome set such that for every density operator $\rho$ on $\mathcal H$ and every event $A\subseteq\Omega$,
--   $$
--   \Pr\big[P'\text{ on }\rho^{\otimes q\ell}\in A\big]=\Pr\big[P\text{ on }(\rho^{\otimes q})^{\otimes k}\in A\big].
--   $$
--   ($P'$ regroups the $q\ell$ copies into $\ell$ blocks of $q$, applies $P$ to the first $k$ blocks and ignores the rest.)
--
--   This lets a measurement whose copy count is only bounded, such as the Gentle Search procedure of Lemma 15 run on amplified registers (p. 16), be used inside a protocol with a fixed copy budget.
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

/-- **K6.** Regrouping and padding copies: a measurement on `k` blocks of `q` copies each
(a POVM on `(ρ^{⊗q})^{⊗k}`) with `k ≤ ℓ` can be run on `q ℓ` copies of `ρ` (ignoring the unused
ones) with exactly the same outcome statistics, for every state `ρ`. -/
theorem povm_lift {n : Type} [Fintype n] [DecidableEq n] {Ω : Type} [Fintype Ω]
    (q k ℓ : ℕ) (hk : k ≤ ℓ) (P : POVM Ω (Fin k → (Fin q → n))) :
    ∃ P' : POVM Ω (Fin (q * ℓ) → n),
      ∀ ρ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ → ∀ A : Ω → Prop,
        P'.prob (tensorPow ρ (q * ℓ)) A = P.prob (tensorPow (tensorPow ρ q) k) A := by
  sorry

end ShadowTomography.UpperBound
