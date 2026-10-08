-- Prove2me | Theorems.Thm_RossQC_Sufficient_lemma_2_1
-- name    : RossQC.Sufficient.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:19.355186+00:00
-- url     : https://prove2.me/theorems/9bcd0e57-15f5-4174-9516-79ca2d86b808
-- title:
--   Lemma 2.1 — concavity of discounted value in the belief
-- statement:
--   In the two-state model, let $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$. For beliefs $P,Q\in[0,1]$ and $\lambda\in[0,1]$,
--   $$
--   V_\beta(\lambda P+(1-\lambda)Q)\ge\lambda V_\beta(P)+(1-\lambda)V_\beta(Q).
--   $$
--
--   Concavity constrains the shape of the producing alternative in the threshold analysis.
--
--   **Formalization Note** Ross states Lemma 2.1 on the general belief simplex. The map $P\mapsto(1-P,P)$ identifies this statement with its two-state instance.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 589, Lemma 2.1; two-state specialization on p. 590

import Definitions.Def_RossQC_Sufficient_Model

namespace RossQC.Sufficient

/-- Ross, Lemma 2.1, p. 589, specialized to the two-state model of §3.
The map from the scalar bad-state probability `P` to belief `(1-P, P)` is
affine, so this is the scalar instance of the paper's general concavity. -/
theorem lemma_2_1 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) M.value := by sorry

end RossQC.Sufficient
