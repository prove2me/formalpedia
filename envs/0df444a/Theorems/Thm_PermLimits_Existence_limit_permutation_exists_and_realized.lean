-- Prove2me | Theorems.Thm_PermLimits_Existence_limit_permutation_exists_and_realized
-- name    : PermLimits.Existence.limit_permutation_exists_and_realized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:04:06.403802+00:00
-- url     : https://prove2.me/theorems/f9682b1d-8db5-4e84-be4d-15cc06ed1a85
-- title:
--   Theorem 1.6: convergent permutation sequences have limit permutations, and every limit permutation is a limit
-- statement:
--   **Theorem 1.6 (Main result).**
--
--   1. Given a convergent permutation sequence $(\sigma_n)_{n\in\mathbb N}$ for which $|\sigma_n|\to\infty$, there exists a limit permutation $Z\in\mathcal Z$ such that $\sigma_n\to Z$.
--   2. Conversely, every $Z\in\mathcal Z$ is a limit of a convergent permutation sequence: there is a sequence $(\sigma_n)_{n\in\mathbb N}$ such that $\sigma_n\to Z$.
--
--   Here a sequence is convergent if every pattern density $t(\tau,\sigma_n)$ converges, and $\sigma_n\to Z$ means $|\sigma_n|\to\infty$ and
--   $$\lim_{n\to\infty}t(\tau,\sigma_n)=t(\tau,Z)\qquad\text{for every permutation }\tau .$$
--
--   The theorem identifies $\mathcal Z$ as the space of limits of permutation sequences, the permutation analogue of the Lovász–Szegedy theorem that graphons are the limits of dense graph sequences.
--
--   **Formalization Note** Both parts form one conjunction. In part 2 the sequence consists of genuine permutations, each of length at least $1$. $\sigma_n\to Z$ includes $|\sigma_n|\to\infty$ and implies that the sequence is convergent.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 4, Theorem 1.6

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_ConvergesTo
open PermLimits.Shared

namespace PermLimits.Existence

open Filter unitInterval

/-- **Theorem 1.6 (Main result)** (Hoppen et al., *Limits of permutation sequences*,
arXiv:1103.5844v2, p. 4).
(i) Given a convergent permutation sequence `(σ_m)` for which `|σ_m| → ∞`, there exists a limit
permutation `Z` such that `σ_m → Z`.
(ii) Conversely, every `Z ∈ 𝒵` is a limit of a convergent permutation sequence, i.e. there is a
sequence `(σ_m)` such that `σ_m → Z`.

**Formalization Note.** The two parts are one conjunction. Convergence of the sequence
(Definition 1.2, `IsConvergent`) is the hypothesis of (i), and `σ_m → Z` (Definition 1.5,
`ConvergesTo`, which includes `|σ_m| → ∞`) its conclusion. In (ii) the sequence consists of
genuine permutations, `|σ_m| ≥ 1` (the paper's `S_n` has `n ≥ 1`); `σ_m → Z` implies that the
sequence is convergent. Sequences are named `s` (`σ` is reserved notation once `unitInterval` is
opened). -/
theorem limit_permutation_exists_and_realized :
    (∀ s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n), IsConvergent s →
        Tendsto (fun m => (s m).1) atTop atTop →
        ∃ Z : I → I → ℝ, IsLimitPerm Z ∧ ConvergesTo s Z) ∧
    (∀ Z : I → I → ℝ, IsLimitPerm Z →
        ∃ s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n), (∀ m, 1 ≤ (s m).1) ∧ ConvergesTo s Z) := by sorry

end PermLimits.Existence
