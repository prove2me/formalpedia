-- Prove2me | Theorems.Thm_PermLimits_Cauchy_eventually_const_of_convergent
-- name    : PermLimits.Cauchy.eventually_const_of_convergent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:26:08.058619+00:00
-- url     : https://prove2.me/theorems/18ac3c75-f3d0-45d3-b776-c1048a1bfc22
-- title:
--   Claim 2.4: a convergent sequence with $|\sigma_n|\not\to\infty$ is eventually constant
-- statement:
--   Let $(\sigma_n)_{n\in\mathbb N}$ be a convergent permutation sequence such that $|\sigma_n|\not\to\infty$. Then $(\sigma_n)$ is eventually constant: there are a permutation $\sigma$ and $n_0\in\mathbb N$ such that
--   $$\sigma_n=\sigma\qquad\text{for all } n\ge n_0 .$$
--
--   Hence the only interesting convergent sequences are those whose lengths tend to infinity; in the metric space of permutations under $d_\square$, permutations are isolated points.
--
--   **Formalization Note** $|\sigma_n|\not\to\infty$ is the negation of "$|\sigma_n|\to\infty$". Equality $\sigma_n=\sigma$ includes equality of lengths. The type admits the empty permutation of length $0$; the statement does not exclude it.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 9, Sect. 2.4, Claim 2.4

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
open PermLimits.Shared

namespace PermLimits.Cauchy

open Filter

/-- **Claim 2.4** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 9).
Let `(σ_n)` be a convergent permutation sequence such that `|σ_n| ↛ ∞`. Then `(σ_n)` is eventually
constant: there is a permutation `σ` and an `n₀ ∈ ℕ` such that `n ≥ n₀` implies `σ_n = σ`.

**Formalization Note.** `|σ_n| ↛ ∞` is the negation of `Tendsto (fun n => |σ_n|) atTop atTop`.
Equality `σ_n = σ` is equality of dependent pairs `⟨length, permutation⟩`, so it includes
equality of lengths. The type also admits the empty permutation (length `0`); the statement is
made without excluding it. -/
theorem eventually_const_of_convergent (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hconv : IsConvergent s) (hs : ¬ Tendsto (fun n => (s n).1) atTop atTop) :
    ∃ (p : Σ n : ℕ, Equiv.Perm (Fin n)) (n₀ : ℕ), ∀ n, n₀ ≤ n → s n = p := by sorry

end PermLimits.Cauchy
