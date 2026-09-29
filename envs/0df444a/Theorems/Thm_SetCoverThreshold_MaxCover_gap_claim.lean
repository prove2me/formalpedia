-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_gap_claim
-- name    : SetCoverThreshold.MaxCover.gap_claim
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:06:57.997658+00:00
-- url     : https://prove2.me/theorems/666debd3-73a0-4e6f-8ff2-18d3b6cf221a
-- title:
--   Gap of the §5 reduction — kQ sets cover all N points, or at most (1 − 1/e + g(k))N
-- statement:
--   Assume the consequence of Raz's parallel repetition theorem stated on p. 642. Consider the max $k'$-cover instance of §5 built from a 3CNF-5 formula $\varphi$, $\ell$ repetitions, $k$ provers and a code, with $N=mR$ points and $k'=kQ$.
--
--   1. If $\varphi$ is satisfiable, all $N$ points can be covered by $kQ$ sets.
--   2. For every $\varepsilon>0$ there is $k_0$ such that for every $k\ge k_0$ and every $\varepsilon'>0$ there is $\ell_0$ such that for all $\ell\ge\ell_0$, every code of $k$ words of length $\ell$, weight $\ell/2$ and distance at least $\ell/3$, and every $\varphi$ in which at most a $(1-\varepsilon')$-fraction of the clauses are simultaneously satisfiable, every collection of at most $kQ$ sets covers at most
--   $$\Big(1-\frac1e+\varepsilon\Big)N$$
--   points.
--
--   Part 2 is the paper's "$kQ$ sets can cover at most $(1-1/e+g(k))N$ points, where $g(k)\to0$ as $k\to\infty$", for "large enough $\ell$". Together the two parts are the gap that Theorem 5.3 exploits with a constant number of repetitions.
--
--   **Formalization Note** "$g(k)\to0$" is rendered as $\forall\varepsilon\,\exists k_0\,\forall k\ge k_0$, with $k_0$ independent of $\varepsilon'$, and "large enough $\ell$" as $\exists\ell_0$ after $k$ and $\varepsilon'$. The budget $kQ$ is the total number of (prover, question) pairs.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 649, proof of Theorem 5.3

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-- **The gap of the §5 reduction** (Feige 1998, p. 649, proof of Theorem 5.3), from the cited
parallel repetition bound. (i) If `φ` is satisfiable, all `N` points of the §5 instance can be
covered by `kQ` sets. (ii) For every `ε > 0` there is `k₀` such that for every `k ≥ k₀` and
every `ε' > 0`, for all large enough `ℓ`: if at most a `(1 − ε')`-fraction of the clauses of
`φ` are simultaneously satisfiable, every collection of at most `kQ` sets covers at most
`(1 − 1/e + ε) N` points. -/
theorem gap_claim (hRaz : RazRepetition) :
    (∀ (k ℓ : ℕ) (code : Fin k → Fin ℓ → Bool) (φ : Formula5), φ.toCNF.Satisfiable →
        ∃ C : Finset (SetIdx φ code), C.card ≤ coverBudget φ code ∧
          coveredMaxCover φ code C = Finset.univ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
        ∀ code : Fin k → Fin ℓ → Bool, IsCode code →
          ∀ φ : Formula5, AtMostFracSat (1 - ε') φ.toCNF →
            ∀ C : Finset (SetIdx φ code), C.card ≤ coverBudget φ code →
              ((coveredMaxCover φ code C).card : ℝ) ≤
                (1 - Real.exp (-1) + ε) *
                  (Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) : ℝ)) := by sorry

end SetCoverThreshold.MaxCover
