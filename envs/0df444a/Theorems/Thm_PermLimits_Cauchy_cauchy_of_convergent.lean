-- Prove2me | Theorems.Thm_PermLimits_Cauchy_cauchy_of_convergent
-- name    : PermLimits.Cauchy.cauchy_of_convergent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:26:53.220566+00:00
-- url     : https://prove2.me/theorems/c89e5eff-66ec-4894-ab48-8990327eaff9
-- title:
--   Theorem 1.8 ($\Rightarrow$): every convergent permutation sequence is $d_\square$-Cauchy
-- statement:
--   Every convergent permutation sequence $(\sigma_n)_{n\in\mathbb N}$ is a Cauchy sequence with respect to the rectangular distance: for every $\varepsilon>0$ there is $n_0$ such that
--   $$d_\square(\sigma_n,\sigma_m)<\varepsilon\qquad\text{for all } n,m\ge n_0 .$$
--
--   No assumption on the lengths $|\sigma_n|$ is made. This is the direction of the source's Theorem 1.8 that holds exactly as stated there; the converse needs $|\sigma_n|\to\infty$.
--
--   **Formalization Note** "Convergent" is the source's Definition 1.2. The rectangular distance between permutations of different lengths is $d_\square(Z_\sigma,Z_\pi)$.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 5, Theorem 1.8 (the "only if" direction); proof p. 18

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Cauchy_RectCauchy
open PermLimits.Shared

namespace PermLimits.Cauchy

/-- **Theorem 1.8, "only if" direction** (Hoppen et al., *Limits of permutation sequences*,
arXiv:1103.5844v2, p. 5; proof p. 18). Every convergent permutation sequence `(σ_n)` is a Cauchy
sequence with respect to the metric `d□`.

**Formalization Note.** No hypothesis on the lengths `|σ_n|` is made: this is the direction of
Theorem 1.8 that holds as the paper states it (by Claim 2.4 when `|σ_n| ↛ ∞`). The converse
direction needs `|σ_n| → ∞`; see the goal theorem `convergent_iff_cauchy_rectangular`. `d□` on
permutations of different lengths is `d□(Z_σ, Z_π)` (`permRectDist`). -/
theorem cauchy_of_convergent (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n)) (hconv : IsConvergent s) :
    IsRectCauchy s := by sorry

end PermLimits.Cauchy
