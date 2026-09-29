-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_prop_5_4
-- name    : SetCoverThreshold.MaxCover.prop_5_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:05:46.820188+00:00
-- url     : https://prove2.me/theorems/495612fa-3a76-4ecc-852a-30455244ee02
-- title:
--   Proposition 5.4 — the fraction of good r is at least ε/3
-- statement:
--   Let $\varepsilon>0$. Then there is $k_0$ such that for every $k\ge k_0$, every $\ell$, every code of $k$ words of length $\ell$, weight $\ell/2$ and pairwise distance at least $\ell/3$, and every 3CNF-5 formula $\varphi$, the following holds in the max $k'$-cover instance of §5 ($N=mR$ points, $m=k^{2^\ell}$, $R=(3M)^\ell$). If a collection $\mathcal C$ of at most $k'=kQ$ sets covers at least $(1-1/e+\varepsilon)N$ points, then
--   $$\#\{r : r \text{ is good}\}\ \ge\ \frac{\varepsilon}{3}\,R,$$
--   where $r$ is *good* if $w_r\le 3k/\varepsilon$ and two sets of $\mathcal C$ with $(q,i),(q',i')\in r$ and $i\ne i'$ induce the same partition label $a_r$.
--
--   In the paper's words: assume that a $(1-1/e+\varepsilon)$-fraction of the points are covered; then the fraction of good $r$ is at least $\varepsilon/3$. It is the §5 analogue of Proposition 4.2.
--
--   **Formalization Note** "For large enough $k$" (from the proof) is $\exists k_0\,\forall k\ge k_0$, with $k_0$ chosen before $\ell$, $\varphi$ and $\mathcal C$. The fraction is stated as a count, which avoids a division by $R$ (and a vacuous failure when $\varphi$ has no clauses). The proof's reference to "Proposition 8" is a typo for Proposition 4.2.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 649, Proposition 5.4

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

/-- **Proposition 5.4** (Feige 1998, p. 649): for every `ε > 0` and all large enough `k`, in
the §5 instance built from a 3CNF-5 formula `φ` and a code (weights `ℓ/2`, distances
`≥ ℓ/3`), every collection of at most `kQ` sets that covers at least a
`(1 − 1/e + ε)`-fraction of the `N` points has at least an `ε/3`-fraction of good random
strings. -/
theorem prop_5_4 (ε : ℝ) (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (ℓ : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode code →
      ∀ (φ : Formula5) (C : Finset (SetIdx φ code)), C.card ≤ coverBudget φ code →
        (1 - Real.exp (-1) + ε) *
            (Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) : ℝ) ≤
          ((coveredMaxCover φ code C).card : ℝ) →
        ε / 3 * (Fintype.card (RandString φ ℓ) : ℝ) ≤ (goodCount φ code ε C : ℝ) := by sorry

end SetCoverThreshold.MaxCover
