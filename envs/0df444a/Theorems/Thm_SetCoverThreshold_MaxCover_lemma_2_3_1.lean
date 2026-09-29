-- Prove2me | Theorems.Thm_SetCoverThreshold_MaxCover_lemma_2_3_1
-- name    : SetCoverThreshold.MaxCover.lemma_2_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:04:20.508693+00:00
-- url     : https://prove2.me/theorems/04af2a5e-f279-48fb-b0f7-430aefa8b4b3
-- title:
--   Lemma 2.3.1 — completeness and soundness of the k-prover proof system
-- statement:
--   Assume the consequence of Raz's parallel repetition theorem stated on p. 642. Let $\varepsilon>0$. Then there is a constant $c>0$, depending only on $\varepsilon$, such that for every 3CNF-5 formula $\varphi$, all $\ell,k$, and every code of $k$ binary words of length $\ell$, weight $\ell/2$ and pairwise Hamming distance at least $\ell/3$, the $k$-prover proof system satisfies:
--
--   1. if $\varphi$ is satisfiable, the provers have a strategy under which the verifier strongly accepts on every random string;
--   2. if at most a $(1-\varepsilon)$-fraction of the clauses of $\varphi$ are simultaneously satisfiable, then under every strategy of the provers
--   $$\Pr_r[\text{the verifier weakly accepts}]\le k^2\cdot 2^{-c\ell}.$$
--
--   The two acceptance predicates give the reduction to max $k$-cover its gap: complete consistency on satisfiable formulas, rare pairwise consistency on far-from-satisfiable ones.
--
--   **Formalization Note** The constant $c$ is quantified before $\varphi$, $\ell$, $k$ and the code. Answers on clause coordinates are canonical (they satisfy the clause), as the paper assumes without loss of generality. The probability is a uniform count over the $(3M)^\ell$ random strings.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 643, Lemma 2.3.1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-- **Lemma 2.3.1** (Feige 1998, p. 643), from the cited parallel repetition bound: for every
`ε > 0` there is `c > 0` such that for every 3CNF-5 formula `φ`, every `ℓ`, `k` and every
code of `k` words of length `ℓ`, weight `ℓ/2` and pairwise distance `≥ ℓ/3`: if `φ` is
satisfiable the provers can make the verifier always strongly accept, and if at most a
`(1 − ε)`-fraction of its clauses are simultaneously satisfiable, the verifier weakly accepts
with probability at most `k^2 · 2^{−cℓ}` under every strategy. -/
theorem lemma_2_3_1 (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode code →
        (φ.toCNF.Satisfiable →
            ∃ strat : Fin k → Strategy φ ℓ, ∀ r, StrongAccept φ code strat r) ∧
        (AtMostFracSat (1 - ε) φ.toCNF →
            ∀ strat : Fin k → Strategy φ ℓ,
              weakAcceptFrac φ code strat ≤ (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ))) := by sorry

end SetCoverThreshold.MaxCover
