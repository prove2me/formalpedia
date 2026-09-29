-- Prove2me | Theorems.Thm_PermLimits_Existence_sample_rectDist_close
-- name    : PermLimits.Existence.sample_rectDist_close
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:02:55.571059+00:00
-- url     : https://prove2.me/theorems/09b69de8-7c31-4e85-9b1d-a78243f977ab
-- title:
--   Lemma 4.2: $\mathbf P\big(d_\square(Z,\sigma(k,Z))\le16k^{-1/4}\big)\ge1-\frac12e^{-\sqrt k}$
-- statement:
--   There is $k_0$ such that for every integer $k\ge k_0$ and every $Z\in\mathcal Z$,
--   $$\mathbf P\big(d_\square(Z,\sigma(k,Z))\le16k^{-1/4}\big)\ge1-\tfrac12e^{-\sqrt k}. \tag{37}$$
--   Here $\sigma(k,Z)$ is the $Z$-random permutation of length $k$ and $d_\square(Z,\sigma)=d_\square(Z,Z_\sigma)$.
--
--   A random sample of size $k$ recovers $Z$ up to rectangular distance $16k^{-1/4}$ with overwhelming probability. Through the Borel–Cantelli lemma it gives the alternative proof of part (ii) of the main theorem.
--
--   **Formalization Note** "$k$ sufficiently large" is $\exists k_0\,\forall k\ge k_0$, with $k_0$ chosen before $Z$: the thresholds in the source's proof do not depend on $Z$. Since $\sigma(k,Z)=\tau$ has probability $t(\tau,Z)$ (Eq. (24)), the probability in (37) is written as $\sum t(\tau,Z)$ over the $\tau\in S_k$ with $d_\square(Z,Z_\tau)\le16k^{-1/4}$. The constants $16$, $-1/4$, $\tfrac12$ and the non-strict inequality are the source's.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 13, Lemma 4.2 (Eq. (37))

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_StepLimit
import Definitions.Def_PermLimits_Shared_RectDist
open PermLimits.Shared

namespace PermLimits.Existence

open unitInterval

/-- **Lemma 4.2** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 13).
If `k ∈ ℕ` is a sufficiently large integer and `Z ∈ 𝒵`, then
`P(d□(Z, σ(k, Z)) ≤ 16 k^{−1/4}) ≥ 1 − ½ e^{−√k}` (Eq. (37)).

**Formalization Note.** "Sufficiently large" is `∃ k₀, ∀ k ≥ k₀`, with `k₀` chosen before `Z`:
the thresholds in the proof (`4/k < k^{−1/4}` and `12 k² e^{−√k} ≤ 1`) do not depend on `Z`.
The `Z`-random permutation `σ(k, Z)` takes the value `τ ∈ S_k` with probability `t(τ, Z)`
(Definition 3.3, Eq. (24)), so the probability of the event `d□(Z, σ(k, Z)) ≤ 16 k^{−1/4}` is the
sum of `t(τ, Z)` over the `τ ∈ S_k` with `d□(Z, Z_τ) ≤ 16 k^{−1/4}` (Eq. (36):
`d□(Z, τ) = d□(Z, Z_τ)`). `k^{−1/4}` is the real power `(k : ℝ) ^ (−1/4 : ℝ)`. -/
theorem sample_rectDist_close :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ Z : I → I → ℝ, IsLimitPerm Z →
      1 - (1 / 2) * Real.exp (-Real.sqrt k) ≤
        ∑ τ ∈ Finset.univ.filter (fun τ : Equiv.Perm (Fin k) =>
            rectDist Z (stepLimit τ) ≤ 16 * (k : ℝ) ^ (-(1 / 4 : ℝ))),
          limitDensity τ Z := by sorry

end PermLimits.Existence
