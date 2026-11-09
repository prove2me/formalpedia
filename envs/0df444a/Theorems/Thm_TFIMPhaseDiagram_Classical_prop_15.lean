-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_prop_15
-- name    : TFIMPhaseDiagram.Classical.prop_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:04:53.306868+00:00
-- url     : https://prove2.me/theorems/df04a704-65ed-4cf5-a2c5-53c41c98e080
-- title:
--   Proposition 15 — Linear-time cycle sampler, including well-defined zero-field limits
-- statement:
--   For arbitrary real cycle couplings and finite or compatible infinite external fields on $M\ge3$ spins, a uniform classical Real RAM program samples the cycle law exactly. The same program handles both parity-cycle families with $\eta\ge0$, whenever their tilted law is well-defined:
--   $$\mathcal L(\widehat s)=\pi_{K,w},\qquad T\le CM,$$
--   for one absolute constant $C$. The zero-field even and odd limiting laws are included explicitly. Exact linear-time cycle sampling supplies each block update.
--
--   Differences from the source:
--   - encoding: a linear-time cycle sampler including well-defined eta=0 limits → one uniform finite Real RAM program, explicit input encoding, budget CM and equality of output laws; reason: The exact target law includes mixed signs, infinite-field pins, and both limiting parity laws.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.9 = PDF p.9, Proposition 15

import Definitions.Def_TFIMPhaseDiagram_Classical_sampling

set_option autoImplicit false

namespace TFIMPhaseDiagram.Classical
/-- Proposition 15, p.9: one exact linear-time sampler for signed cycles and both eta=0 limits. -/
theorem prop_15 : ∃ (P : RAMProgram) (C : ℕ), Admissible P ∧ 0 < C ∧
  ∀ M : ℕ, 3 ≤ M → ∀ (K : CycleParameters M) (w : Fin M → Field),
    ValidCycle K w → SamplesCycle P (C*M) K w := by sorry
end TFIMPhaseDiagram.Classical
