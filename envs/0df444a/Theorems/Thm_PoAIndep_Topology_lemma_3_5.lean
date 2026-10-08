-- Prove2me | Theorems.Thm_PoAIndep_Topology_lemma_3_5
-- name    : PoAIndep.Topology.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:20.104011+00:00
-- url     : https://prove2.me/theorems/b8c73690-daf8-4113-91f5-c85aa75dac12
-- title:
--   Lemma 3.5, p. 11 — C(f*) ≥ Σₑ [ℓₑ(λₑfₑ)λₑfₑ + (f*ₑ − λₑfₑ)ℓₑ(fₑ)] when ℓ*ₑ(λₑfₑ) = ℓₑ(fₑ)
-- statement:
--   Let $(G,r,\ell)$ be an instance with standard latency functions, and let $f$ and $f^*$ be flows with edge flows $f_e$ and $f^*_e$. For each edge $e$ let $\lambda_e\in[0,1]$ satisfy $\ell_e^*(\lambda_e f_e)=\ell_e(f_e)$. Then
--   $$C(f^*)\ge\sum_{e\in E}\Bigl[\ell_e(\lambda_e f_e)\,\lambda_e f_e+(f^*_e-\lambda_e f_e)\,\ell_e(f_e)\Bigr].$$
--
--   In the paper $f$ is a Nash flow and $f^*$ an optimal flow; the lemma splits the cost of $f^*$ into the cost of the scaled-down pseudoflow $\{\lambda_e f_e\}$ and an augmentation priced at marginal cost $\ell_e(f_e)$. The page remarks that $f^*_e-\lambda_e f_e$ may have either sign.
--
--   **Formalization Note.** The page assumes $f$ Nash and $f^*$ optimal, but neither the statement's inequality nor its proof uses these properties; the formal statement assumes only that $f$ and $f^*$ are flows (nonnegative, on simple paths), which makes it more general.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 11, Lemma 3.5

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem lemma_3_5 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (hstd : ∀ e, IsStandard (I.ℓ e)) (f g : Flow I)
    (hf : IsFlow I f) (hg : IsFlow I g) (lam : E → ℝ)
    (hlam : ∀ e, lam e ∈ Set.Icc (0 : ℝ) 1 ∧
      marginalCost (I.ℓ e) (lam e * edgeFlow I f e) = I.ℓ e (edgeFlow I f e)) :
    ∑ e, (I.ℓ e (lam e * edgeFlow I f e) * (lam e * edgeFlow I f e) +
        (edgeFlow I g e - lam e * edgeFlow I f e) * I.ℓ e (edgeFlow I f e)) ≤ cost I g := by sorry

end PoAIndep.Topology
