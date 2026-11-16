-- Prove2me | Theorems.Thm_RandPurIso_Completion_Supplement_theorem_A_1
-- name    : RandPurIso.Completion.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:58:07.959+00:00
-- url     : https://prove2.me/theorems/ed4182b1-b9e5-4222-a88f-5bdc8e58f4ad
-- title:
--   Theorem A.1 — the classically controlled switch is within trace distance $1/2$ of $\mathrm{Sw}[\Phi,\Psi]$
-- statement:
--   Let $\Phi(\rho)=\sum_aK_a\rho K_a^\dagger$ and $\Psi(\rho)=\sum_bK'_b\rho K_b'^\dagger$ be any two channels on a common finite-dimensional space $X$ ($\sum_aK_a^\dagger K_a=I$, $\sum_bK_b'^\dagger K'_b=I$). Let $\widetilde{\mathrm{Sw}}[\Phi,\Psi]$ be the classically controlled switch, which measures the control and applies the channels in the order it selects, using one forward query to each channel. Then for every finite reference register $R$ and every density matrix $\rho$ on $(\mathbf C\otimes X)\otimes R$,
--
--   $$
--   \mathrm{TD}\Big(\big(\mathrm{Sw}[\Phi,\Psi]\otimes\mathrm{id}_R\big)(\rho),\ \big(\widetilde{\mathrm{Sw}}[\Phi,\Psi]\otimes\mathrm{id}_R\big)(\rho)\Big)\le\frac12 .
--   $$
--
--   So the quantum switch can be simulated with one query to each channel and classically controlled causal order, with error at most $1/2$ on every input, including inputs entangled with a reference. By Corollary 7.2 this error cannot be pushed below $1/2$ with few forward queries.
--
--   **Formalization Note** Channels are given by Kraus families over arbitrary finite index sets; $\mathrm{Sw}$ is built from them and $\widetilde{\mathrm{Sw}}$ from the channel maps only. $R$ ranges over all finite types (a one-point $R$ gives inputs without reference).
--
--   Differences from the source:
--   - generalization: the switch can be simulated with one forward query to each channel and classically controlled causal order, with error ≤ 1/2 → the error bound ≤ 1/2 for the specific simulation classicalSwitch (measure C, then Ψ∘Φ or Φ∘Ψ), the one in the proof; reason: exhibits a witness of the page's existential claim; the witness uses one query to each channel map and classical control
--   - encoding: any channels Φ, Ψ on a common space; every input, including inputs entangled with an arbitrary reference register → Kraus families K, K' on a finite type X with Σ K†K = 1; every finite R and every density matrix on (C ⊗ X) ⊗ R, maps applied ⊗ id_R; reason: every channel has a Kraus family; same instances
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem A.1, p. 64 (Appendix A)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_RandPurIso_Completion_traceDist
import Definitions.Def_RandPurIso_Completion_Supplement_qswitch
import Definitions.Def_RandPurIso_Completion_Supplement_classicalSwitch
open Matrix

namespace RandPurIso.Completion.Supplement

open RandPurIso.Completion

/-- **Theorem A.1** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Appendix A, p. 64).

For any channels `Φ` and `Ψ` on a common space, the quantum switch `Sw[Φ, Ψ]` can be simulated using
one forward query to each channel and classically controlled causal order, with trace-distance error
at most `1/2` on every input, including inputs entangled with an arbitrary reference register.

**Formalization Note.**
* Channels are given by Kraus families `K` (for `Φ`) and `K'` (for `Ψ`) over arbitrary finite index
  types on one finite space `X`, with `Σ K†K = 1`; every channel has such a family.
* The simulation is the one of the proof: the classically controlled switch `classicalSwitch Φ Ψ`
  (measure the control, then apply `Ψ ∘ Φ` on outcome 0 and `Φ ∘ Ψ` on outcome 1), which uses one
  query to each channel map. Stating the bound for this simulation implies the page's existence claim.
* "Every input, including inputs entangled with a reference": every finite reference register `R`
  and every density matrix on `(C ⊗ X) ⊗ R`, both maps applied as `⊗ id_R` (`PeresTerno.ampliate`).
  `R = Unit` gives inputs without reference. -/
theorem theorem_A_1 :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (ι κ : Type) [Fintype ι] [Fintype κ]
      (K : ι → Matrix X X ℂ) (K' : κ → Matrix X X ℂ),
      ∑ a, (K a)ᴴ * K a = 1 → ∑ b, (K' b)ᴴ * K' b = 1 →
      ∀ (R : Type) [Fintype R] [DecidableEq R] (ρ : Matrix ((Bool × X) × R) ((Bool × X) × R) ℂ),
        PeresTerno.IsDensityMatrix ρ →
        traceDist (PeresTerno.ampliate (qswitch K K') ρ)
          (PeresTerno.ampliate
            (classicalSwitch (PeresTerno.krausUpdate K) (PeresTerno.krausUpdate K')) ρ) ≤ 1 / 2 := by sorry

end RandPurIso.Completion.Supplement
