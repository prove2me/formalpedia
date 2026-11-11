-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_lemma_6_7
-- name    : QMA2ClassicalSep.Main.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:24.868067+00:00
-- url     : https://prove2.me/theorems/b6043339-3789-4c81-b0c6-2c6a30f21d4a
-- title:
--   Lemma 6.7 — independence of the peeling choices
-- statement:
--   Let $k\ge2$ and let $(D,S)$ be a record with $|\mathrm{coords}(D)\cup S|<N/2$. For every execution of Algorithm 1 on $(D,S)$, with output $(C,F,L)$, and every pair-labeling $\theta$, the amplitude
--
--   $$
--   \gamma_C(\theta)\,\gamma_F(\theta)\prod_{(e,b_e)\in L}\lambda_e(\theta)
--   $$
--
--   equals the completion amplitude $a_{D,S}(\theta)$. The amplitude therefore depends neither on the order in which entries are removed nor on the orientations chosen, so Definition 6.6 is well defined.
--
--   Differences from the source:
--   - reading: |coords(D) ∪ S| < N2 and "does not depend on the order … nor on the orientations" → 2·|coords(D) ∪ S| < N, and every execution gives the value of the canonical execution used to define a_{D,S}; reason: the printed N2 is N/2 (as in Lemma 6.8 and the admissibility condition); equality with one fixed execution is equivalent to independence of the choices
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 32, Lemma 6.7 (proof p. 33)

import Definitions.Def_QMA2ClassicalSep_Main_Completion

namespace QMA2ClassicalSep.Main

theorem lemma_6_7 (k : ℕ) (hk : 2 ≤ k) (D : Finset (Entry k)) (S : Finset (HCoord k))
    (hD : IsDatabase D) (hadm : Admissible D S) (θ : Labeling k)
    (L : List (Entry k × Bool × Bool)) (C : Finset (Entry k)) (Sf : Finset (HCoord k))
    (hrun : PeelRun D S L C Sf) :
    ampOfRun θ L C Sf = complAmp D S θ := by sorry

end QMA2ClassicalSep.Main
