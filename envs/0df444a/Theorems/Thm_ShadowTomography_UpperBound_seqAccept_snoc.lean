-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_seqAccept_snoc
-- name    : ShadowTomography.UpperBound.seqAccept_snoc
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:15.998127+00:00
-- url     : https://prove2.me/theorems/c388577a-a2bf-44a2-906e-625eae6eb242
-- title:
--   Appending one measurement to a Lüders sequence
-- statement:
--   Let $F_0,\dots,F_{M-1}$ be operators on $\mathcal H$, let $G$ be an effect ($0\preceq G\preceq I$) and $\sigma$ a matrix. With $A=\sqrt{F_{M-1}}\cdots\sqrt{F_0}$, the probability that $F_0,\dots,F_{M-1},G$ applied in succession by Lüders instruments all accept is
--   $$
--   \operatorname{acc}(F_0,\dots,F_{M-1},G;\sigma)=\operatorname{Re}\operatorname{Tr}\big(G\,A\sigma A^\dagger\big).
--   $$
--   Equivalently, it is the acceptance probability of $G$ on the unnormalised post-selected state $A\sigma A^\dagger$.
--
--   This telescoping identity is how the potential $p_t=\operatorname{Tr}(F_0\sigma_0)\cdots\operatorname{Tr}(F_{t-1}\sigma_{t-1})$ of the shadow-tomography algorithm is related to the post-selected hypotheses $\sigma_t$ (p. 17).
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

/-- **K4b.** Appending one more effect `G` to a Lüders sequence: the probability that all of
`F 0, …, F (M-1), G` accept equals `Tr(G · A σ A†)` with `A = √F_{M-1} ⋯ √F_0`
(the unnormalised post-selected state). -/
theorem seqAccept_snoc {n : Type} [Fintype n] [DecidableEq n] {M : ℕ}
    (F : Fin M → Matrix n n ℂ) (G : Matrix n n ℂ) (hG : IsEffect G) (σ : Matrix n n ℂ) :
    seqAccept (Fin.snoc (α := fun _ => Matrix n n ℂ) F G) σ =
      (G * (((List.finRange M).reverse.map (fun i => CFC.sqrt (F i))).prod * σ *
        (((List.finRange M).reverse.map (fun i => CFC.sqrt (F i))).prod).conjTranspose)).trace.re := by
  sorry

end ShadowTomography.UpperBound
