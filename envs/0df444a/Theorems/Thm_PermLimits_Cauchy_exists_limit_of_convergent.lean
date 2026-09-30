-- Prove2me | Theorems.Thm_PermLimits_Cauchy_exists_limit_of_convergent
-- name    : PermLimits.Cauchy.exists_limit_of_convergent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:25:36.879252+00:00
-- url     : https://prove2.me/theorems/24426714-1246-43b9-9096-6ce20d5639d2
-- title:
--   Theorem 1.6 (i): a convergent sequence with $|\sigma_n|\to\infty$ has a limit permutation
-- statement:
--   Let $(\sigma_n)_{n\in\mathbb N}$ be a convergent permutation sequence with $|\sigma_n|\to\infty$. Then there is a limit permutation $Z\in\mathcal Z$ with
--   $$\sigma_n\to Z,\qquad\text{that is,}\qquad \lim_{n\to\infty}t(\tau,\sigma_n)=t(\tau,Z)\ \text{for every permutation }\tau .$$
--
--   This is the existence half of the main result of the source. In the Cauchy characterization it supplies the limit permutation of a convergent sequence, from which the Cauchy property follows.
--
--   **Formalization Note** "Convergent" is the source's Definition 1.2 (every density sequence converges) and $\sigma_n\to Z$ its Definition 1.5, which includes $|\sigma_n|\to\infty$. The same statement is part of the goal of the companion mission on the existence of limits; it is restated here in this mission's own namespace.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 4, Theorem 1.6 (i)

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_ConvergesTo
open PermLimits.Shared

namespace PermLimits.Cauchy

open Filter unitInterval

/-- **Theorem 1.6 (i)** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2,
p. 4). Given a convergent permutation sequence `(σ_m)` for which `|σ_m| → ∞`, there exists a
limit permutation `Z` such that `σ_m → Z` holds.

**Formalization Note.** Convergence of the sequence is Definition 1.2 (`IsConvergent`); `σ_m → Z`
is Definition 1.5 (`ConvergesTo`, which includes `|σ_m| → ∞`). The sequence is named `s` (`σ` is
reserved notation once `unitInterval` is opened). This is part (i) of the goal theorem of the
companion mission *Limits of Permutation Sequences I*, restated in this mission's namespace. -/
theorem exists_limit_of_convergent (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n)) (hconv : IsConvergent s)
    (hs : Tendsto (fun m => (s m).1) atTop atTop) :
    ∃ Z : I → I → ℝ, IsLimitPerm Z ∧ ConvergesTo s Z := by sorry

end PermLimits.Cauchy
