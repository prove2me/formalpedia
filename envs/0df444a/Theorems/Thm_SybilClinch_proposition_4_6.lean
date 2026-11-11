-- Prove2me | Theorems.Thm_SybilClinch_proposition_4_6
-- name    : SybilClinch.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:40:21.960845+00:00
-- url     : https://prove2.me/theorems/b96647cf-0c47-4a68-b9bb-a762578225a0
-- title:
--   Proposition 4.6 — the AMM chord target is an admissible target-based mechanism with unattained capacity
-- statement:
--   Let $\varphi$ be an admissible AMM with spot price $p_0$ and pool cost $C$. Then the target-based mechanism
--   $$\mathcal T_{\rm amm}=(p_0,\sigma_{\rm amm},T^{\rm amm},D_{\rm amm},x_0),\qquad D_{\rm amm}=\{(p,X,Y):p\ge p_0,\ 0\le X<x_0,\ Y\ge C(X)\},$$
--   with the chord target $T^{\rm amm}(p,X,Y)=\max\{z\in[X,x_0):C(z)\le Y+p(z-X)\}$, is an admissible abstract target-based mechanism (Definition 4.2), and its capacity is never attained: $T^{\rm amm}(p,X,Y)<x_0$ at every state of $D_{\rm amm}$.
--
--   This is what lets the general Sybil-proofness and single-run results of §4 apply to the AMM auction of §3.
--
--   Differences from the source:
--   - encoding: environment description σ in T = (p⋆, σ, T_σ, D_σ, X_σ) → TargetMech with T : ℝ → ℝ → ℝ → ℝ; σ folded into the price argument; reason: Definition 4.1 item 2: the explicit price argument selects any clock-indexed information contained in σ; same instances
--   - reading: clock map locally absolutely continuous away from its jumps (Definition 4.2(4)) → absolutely continuous on every compact price interval of the domain on which it is continuous; reason: the source does not define the phrase further; this is its direct reading
--   - encoding: second sentence: its target-based clinching mechanism is the mechanism of Section 3 → not a separate conclusion: IsRun applied to chordMech A.C A.p0 A.x0 is the §3 mechanism by construction; reason: the sentence is definitional under the substitution (29)
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.3, Proposition 4.6, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_SybilClinch_chordMech
import Definitions.Def_SybilClinch_TargetMech_Admissible
import Definitions.Def_SybilClinch_AdmissibleAMM_C
import Definitions.Def_SybilClinch_AdmissibleAMM_p0

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.3, Proposition 4.6 (Admissibility of the AMM target specification), printed p.16
(PDF p.18).

For an admissible AMM, `T_amm = (p₀, σ_amm, T^amm, D_amm, x₀)`, with
`D_amm = {(p, X, Y) : p ≥ p₀, 0 ≤ X < x₀, Y ≥ C(X)}`, is an admissible abstract target-based
mechanism with unattained capacity: `T^amm < x₀` at every state of `D_amm`.

**Formalization Note.** `T_amm` is `chordMech A.C A.p0 A.x0`. The second sentence of the
proposition (its target-based clinching mechanism is the mechanism of §3) holds by construction:
`IsRun` is the §3 mechanism after the substitution (29). -/
theorem proposition_4_6 (A : AdmissibleAMM) :
    (chordMech A.C A.p0 A.x0).Admissible ∧
      ∀ s ∈ (chordMech A.C A.p0 A.x0).D, (chordMech A.C A.p0 A.x0).T s.1 s.2.1 s.2.2 < A.x0 := by sorry

end SybilClinch
