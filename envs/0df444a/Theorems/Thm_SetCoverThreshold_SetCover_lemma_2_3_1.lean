-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_lemma_2_3_1
-- name    : SetCoverThreshold.SetCover.lemma_2_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:56:53.408965+00:00
-- url     : https://prove2.me/theorems/162608a6-f2eb-4696-babd-8616cf3c7c6a
-- title:
--   Lemma 2.3.1 — completeness and soundness of the $k$-prover proof system
-- statement:
--   Assume the consequence of Raz's parallel repetition theorem (Theorem 2.2.2) for the two-prover system of §2.2 (the proposition `RazRepetition`). Fix $\varepsilon>0$. Then there is a constant $c>0$, depending only on $\varepsilon$, such that the following holds for every 3CNF-5 formula $\varphi$, every $\ell$ and $k$, and every code of $k$ words of length $\ell$ with weight $\ell/2$ and pairwise Hamming distance at least $\ell/3$. For the $k$-prover proof system defined by $\varphi$ and the code:
--
--   1. if $\varphi$ is satisfiable, the provers have a strategy that causes the verifier to always strongly accept (every pair of provers is consistent on every random string);
--   2. if at most a $(1-\varepsilon)$-fraction of the clauses of $\varphi$ are simultaneously satisfiable, then for every strategy of the provers
--
--   $$\Pr_r[\text{the verifier weakly accepts}]\ \le\ k^2\cdot 2^{-c\ell}.$$
--
--   The gap between the strong acceptance of true inputs and the rare weak acceptance of false inputs is what the reduction to set cover converts into a gap in cover size.
--
--   **Formalization Note** The constant $c$ is quantified before the formula, $\ell$, $k$ and the code. Probabilities are uniform counts over random strings; strategies are deterministic and answers canonical. Weak acceptance requires two different provers to be consistent.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 643, Lemma 2.3.1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem

namespace SetCoverThreshold.SetCover

theorem lemma_2_3_1 (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode ℓ k code →
        (φ.toCNF.Satisfiable → ∃ A : φ.KStrategy ℓ k, ∀ r, φ.StrongAccept code A r) ∧
          (AtMostFracSat (1 - ε) φ.toCNF → ∀ A : φ.KStrategy ℓ k,
            φ.weakAcceptFrac code A ≤ (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ))) := by sorry

end SetCoverThreshold.SetCover
