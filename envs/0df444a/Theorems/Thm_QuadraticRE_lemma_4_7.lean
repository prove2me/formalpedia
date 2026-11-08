-- Prove2me | Theorems.Thm_QuadraticRE_lemma_4_7
-- name    : QuadraticRE.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:15:44.487486+00:00
-- url     : https://prove2.me/theorems/6481e94f-76ae-48e1-92a7-ceb4982ee4e6
-- title:
--   Lemma 4.7 — privacy error at most $\min\{1,2q^*_j+2p_j\}$
-- statement:
--   For every $j\ge0$, $h\ge3$ and every $(a,b,c,d)\in\mathbb F_2^4$, the simulator $\mathrm{Sim}_{j,h}(y)=E_{j,h}(0,0,0,y;R')$ satisfies
--   $$\mathrm{SD}\bigl(E_{j,h}(a,b,c,d;R),\,\mathrm{Sim}_{j,h}(abc+d)\bigr)\le\min\{1,\,2q^*_j+2p_j\}.$$
--
--   This reduces privacy to the two reconstruction probabilities of (8).
--
--   Differences from the source:
--   - reading: E_{j,h} has simulator Sim_{j,h} → the simulator Sim_{j,h}(y) = E_{j,h}(0,0,0,y;R′) of p.20, named; reason: the page's Sim_{j,h} is this object, defined in the proof of Proposition 4.4 and used in the proof
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Lemma 4.7, p.23

import Mathlib
import Definitions.Def_QuadraticRE_encE
import Definitions.Def_QuadraticRE_pj

namespace QuadraticRE

/-- Lemma 4.7 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.23: for the concrete simulator `Sim_{j,h}` of p.20 and every input,
`SD(E_{j,h}(a, b, c, d; R), Sim_{j,h}(abc + d)) ≤ min{1, 2q*_j + 2p_j}`. -/
theorem lemma_4_7 (j h : ℕ) (hh : 3 ≤ h) (a b c d : F2) :
    SD (law (encE j h a b c d)) (law (simE j h (a * b * c + d)))
      ≤ min 1 (2 * qStar j + 2 * pj j) := by sorry

end QuadraticRE
