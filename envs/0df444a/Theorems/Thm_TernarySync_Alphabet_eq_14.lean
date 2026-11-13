-- Prove2me | Theorems.Thm_TernarySync_Alphabet_eq_14
-- name    : TernarySync.Alphabet.eq_14
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T03:54:35.659939+00:00
-- url     : https://prove2.me/theorems/0a3a499c-2bb2-4caa-85ba-82680ee06383
-- title:
--   Eq. (14) — every long bad event has $\Pr[E_{t,\ell}] < e^{-9\ell/500}$
-- statement:
--   Fix a square-free outer word $T$ of length $N$ over $\{0,1,2\}$, let $R$ be uniform on $\{0,1\}^N$ and $W = W(T,R)$. For every integer $\ell > 1000$ and every available start $t$, the bad event $E_{t,\ell} = \{\mathrm{LCS}(W[t,t+\ell), W[t+\ell,t+2\ell)) > (1-\eta)\ell\}$ with $\eta = 1/1000$ satisfies
--
--   $$\Pr[E_{t,\ell}] < e^{-9\ell/500}. \tag{14}$$
--
--   It combines Lemma 4.2 with the deletion-ball bound (12): the bad event given $F = f$ is $X \in B_\ell(y)$ for the fixed $y$, so $\Pr[E_{t,\ell} \mid F = f] \le |B_\ell(y)|\,2^{-s}$, and averaging over $f$ gives (14).
--
--   **Formalization Note.** Indices are 0-based ($t + 2\ell \le 18N$); `unifProb` is the uniform probability $|A|/2^N$ on choice vectors.
--
--   Differences from the source:
--   - encoding: 1-based half-open factors $S[i,j)$ with $1 \le i \le j \le n+1$ → 0-based `factor S i j` = positions $i,\dots,j-1$, so the ranges shift by one (e.g. $k \le n+1$ becomes $k \le n$); reason: index shift only; the same factors and the same instances
--   - encoding: R independent fair bits; Pr[E_{t,ℓ}] → unifProb (badEvent T t ℓ), the count ratio |A|/2^N; reason: the uniform measure on a finite set is the count ratio
--   - encoding: the standing setting of §4: T a fixed finite square-free outer word, ℓ > L = 1000 an integer, t an available start → hypotheses IsSquareFree T, 1000 < ℓ, t + 2ℓ ≤ 18|T|; reason: the section's standing assumptions written as binders
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 16 (PDF 17), §4, Eq. (14)

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Equation (14) (p. 16): for a square-free outer word `T`, an integer `ℓ > 1000` and an
available start `t` (0-based, `t + 2ℓ ≤ 18 |T|`), the bad event
`E_{t,ℓ} = {LCS(X, Y) > (1 − 1/1000)ℓ}` has probability `Pr[E_{t,ℓ}] < e^{−9ℓ/500}` under
independent fair bits `R`. -/
theorem eq_14 (T : List (Fin 3)) (hT : IsSquareFree T) (t ℓ : ℕ) (hℓ : 1000 < ℓ)
    (ht : t + 2 * ℓ ≤ 18 * T.length) :
    unifProb (badEvent T t ℓ) < Real.exp (-(9 * (ℓ : ℝ)) / 500) := by sorry

end TernarySync.Alphabet
