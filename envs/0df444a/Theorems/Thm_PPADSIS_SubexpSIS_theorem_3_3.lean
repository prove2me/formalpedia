-- Prove2me | Theorems.Thm_PPADSIS_SubexpSIS_theorem_3_3
-- name    : PPADSIS.SubexpSIS.theorem_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:50:58.993829+00:00
-- url     : https://prove2.me/theorems/9130ef2a-25b2-4e62-a33c-46f0d2f5dd53
-- title:
--   Theorem 3.3 ([CHK+19a]) — a randomized Karp reduction from RSVL to EOML with deterministic instance map
-- statement:
--   There is a randomized Karp reduction $(R_1,R_2)$ from RSVL to EOML with success probability $|I|^{-O(1)}$, in which the instance map $R_1$ is deterministic: $R_1$ is computed in deterministic polynomial time, $R_2$ is probabilistic polynomial time, and there is a constant $c$ such that for every RSVL instance $I$ satisfying the promise, $R_1(I)$ satisfies the EOML guarantee and, for every solution $z$ of $R_1(I)$,
--   $$\Pr\bigl[R_2(I,z)\text{ is an RSVL solution of }I\bigr]\ge(|I|+2)^{-c}.$$
--
--   The theorem is cited from Choudhuri, Hubáček, Kamath, Pietrzak, Rosen and Rothblum ([CHK+19a]; see also [BCH+22]); the paper does not prove it. It transfers hardness: if $D$ is a hard distribution of RSVL, then $R_1(D)$ is a hard distribution of EOML, since composing a solver for $R_1(D)$ with $R_2$ loses only a polynomial factor in its success probability.
--
--   Differences from the source:
--   - reading: "randomized Karp reduction ... with success probability $|I|^{-O(1)}$" (not defined in the paper) → deterministic polynomial-time $R_1$ preserving promise to guarantee, probabilistic polynomial-time $R_2$, success at least $(|I|+2)^{-c}$ for every solution of $R_1(I)$; reason: the paragraph after Theorem 3.3 (p. 21) describes exactly this.
--   - encoding: $|I|^{-O(1)}$ → $(|I|+2)^{-c}$ with $|I|$ the description length; reason: equivalent for $|I|\ge2$, and avoids $|I|\in\{0,1\}$.
--   - encoding: the verifier reads the index $i\in[0,2^m-1]$ as $m$ bits big-endian; RSVL solutions are output as $0v$ (sink) or $1\,v\,\mathrm{bin}_m(i)$ (false positive); instances by fixed descriptions; reason: the paper fixes no encoding.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 21, Theorem 3.3 and the paragraph after it (citing [CHK+19a], [BCH+22])

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_KarpReduction

namespace PPADSIS.SubexpSIS

theorem theorem_3_3 :
    ∃ (R1 : RSVLInstance → EOMLInstance) (R2 : CoinAlg decoderCode),
      IsRandKarpRSVLtoEOML R1 R2 := by sorry

end PPADSIS.SubexpSIS
