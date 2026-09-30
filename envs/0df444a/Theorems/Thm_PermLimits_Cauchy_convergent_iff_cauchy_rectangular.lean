-- Prove2me | Theorems.Thm_PermLimits_Cauchy_convergent_iff_cauchy_rectangular
-- name    : PermLimits.Cauchy.convergent_iff_cauchy_rectangular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:27:25.807636+00:00
-- url     : https://prove2.me/theorems/0891e0ff-f95f-451e-83ff-4f05c579be31
-- title:
--   Theorem 1.8 (corrected): for $|\sigma_n|\to\infty$, convergence $\iff$ $d_\square$-Cauchy
-- statement:
--   Let $(\sigma_n)_{n\in\mathbb N}$ be a permutation sequence with $|\sigma_n|\to\infty$. Then
--   $$(\sigma_n)\ \text{is convergent}\iff (\sigma_n)\ \text{is a Cauchy sequence with respect to } d_\square .$$
--
--   Here "convergent" means that $t(\tau,\sigma_n)$ converges for every permutation $\tau$, and $d_\square(\sigma,\pi)=d_\square(Z_\sigma,Z_\pi)$ is the rectangular distance between permutations of possibly different lengths. The theorem identifies convergence defined by pattern densities with a purely metric notion; it is the statement that the completion of $(\mathcal S,d_\square)$ is the space of limit permutations up to almost-everywhere equality.
--
--   **Formalization Note (correction)** The source states Theorem 1.8 for every permutation sequence. Without $|\sigma_n|\to\infty$ the implication "Cauchy $\Rightarrow$ convergent" fails: for $\sigma=(1,2)\in S_2$ and permutations $\tau_k$ with $|\tau_k|\to\infty$ and $d_\square(Z_{\tau_k},Z_\sigma)\to0$, the sequence $\sigma,\tau_1,\sigma,\tau_2,\dots$ is $d_\square$-Cauchy, but $t(\sigma,\sigma)=1$ while $t(\sigma,\tau_k)\to t(\sigma,Z_\sigma)=3/4$. The source's proof begins "By Claim 2.4 we may assume that $|\sigma_n|\to\infty$", which is valid only for the other implication; that implication is stated without the length assumption as a separate theorem. "Convergent" does not assert the existence of a limit permutation.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 5, Theorem 1.8 (and the definition of a Cauchy sequence above it); proof p. 18

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Cauchy_RectCauchy
open PermLimits.Shared

namespace PermLimits.Cauchy

open Filter

/-- **Theorem 1.8, corrected** (Hoppen et al., *Limits of permutation sequences*,
arXiv:1103.5844v2, p. 5; proof p. 18). A permutation sequence `(σ_n)` with `|σ_n| → ∞` converges
(Definition 1.2) if and only if it is a Cauchy sequence with respect to the metric `d□`.

**Formalization Note (correction).** The paper states Theorem 1.8 for every permutation sequence.
Without `|σ_n| → ∞` the "if" direction is false: for `σ = id ∈ S₂` and permutations `τ_k` with
`|τ_k| → ∞` and `d□(Z_{τ_k}, Z_σ) → 0` (which exist by Lemma 4.2), the sequence
`σ, τ₁, σ, τ₂, …` is `d□`-Cauchy, while `t(σ, σ) = 1` and `t(σ, τ_k) → t(σ, Z_σ) = 3/4`, so it
is not convergent. The paper's reduction "By Claim 2.4 we may assume that `|σ_n| → ∞`" (p. 18) is
valid only for the "only if" direction, which is stated without the length hypothesis as the
separate theorem `cauchy_of_convergent`. "Converges" is Definition 1.2 (`IsConvergent`: every
density sequence converges); it does not assert a limit permutation. `d□` on permutations of
different lengths is `d□(Z_σ, Z_π)` (`permRectDist`, Sect. 4.1, pp. 12–13). The sequence is named
`s`. -/
theorem convergent_iff_cauchy_rectangular (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun n => (s n).1) atTop atTop) :
    IsConvergent s ↔ IsRectCauchy s := by sorry

end PermLimits.Cauchy
