-- Prove2me | Theorems.Thm_PermLimits_Cauchy_converges_iff_stepLimit_densityConv
-- name    : PermLimits.Cauchy.converges_iff_stepLimit_densityConv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:23:01.273652+00:00
-- url     : https://prove2.me/theorems/fb9eec4e-0195-42c7-b13a-63bef3f19c1b
-- title:
--   Eq. (49): $\sigma_n\to Z\iff Z_{\sigma_n}\xrightarrow{t}Z$
-- statement:
--   Let $(\sigma_n)$ be a permutation sequence with $|\sigma_n|\to\infty$ and let $Z\in\mathcal Z$. Then
--   $$\sigma_n\to Z\iff Z_{\sigma_n}\xrightarrow{t}Z . \tag{49}$$
--
--   Convergence of a permutation sequence to $Z$ is thereby reduced to convergence of limit permutations in the density sense.
--
--   **Formalization Note** $|\sigma_n|\to\infty$ is the standing assumption stated in the sentence preceding (49).
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 17, Sect. 5.2, Eq. (49)

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_ConvergesTo
import Definitions.Def_PermLimits_Shared_StepLimit
import Definitions.Def_PermLimits_Shared_LimitConvergence
open PermLimits.Shared

namespace PermLimits.Cauchy

open Filter unitInterval

/-- **Eq. (49)** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2,
Sect. 5.2, p. 17). For a permutation sequence `(σ_m)` with `|σ_m| → ∞` and `Z ∈ 𝒵`,
`σ_m → Z ⟺ Z_{σ_m} →ᵗ Z`.

**Formalization Note.** The sequence is named `s` (`σ` is reserved notation once `unitInterval`
is opened). `|σ_m| → ∞` is the standing assumption the paper sets in the sentence before (49).
-/
theorem converges_iff_stepLimit_densityConv (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun m => (s m).1) atTop atTop) (Z : I → I → ℝ) (hZ : IsLimitPerm Z) :
    ConvergesTo s Z ↔ DensityConv (fun m => stepLimit (s m).2) Z := by sorry

end PermLimits.Cauchy
