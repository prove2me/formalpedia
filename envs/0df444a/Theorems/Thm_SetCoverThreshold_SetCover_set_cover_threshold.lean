-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_set_cover_threshold
-- name    : SetCoverThreshold.SetCover.set_cover_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:59:52.549306+00:00
-- url     : https://prove2.me/theorems/4a56b6a1-fda8-4f65-8f2d-d18d41508528
-- title:
--   Theorem 4.4 — a $(1-\varepsilon)\ln n$ approximation for set cover puts NP in $\mathrm{TIME}(n^{O(\log\log n)})$
-- statement:
--   Assume the three cited results the proof uses:
--
--   1. Theorem 2.1.1 (Arora et al. 1992; Papadimitriou–Yannakakis 1991): MAX 3SAT-B is gap NP-hard (`Thm211`);
--   2. Raz's parallel repetition theorem (Theorem 2.2.2, Raz 1995), in its consequence for the clause–variable game of §2.2 (`RazRepetition`);
--   3. the deterministic construction of partition systems of Naor, Schulman and Srinivasan (1995, Theorem 9), as described on p. 644 (`NaorPartitionSystems`).
--
--   Let $\varepsilon>0$ and suppose a deterministic polynomial-time algorithm approximates set cover within $(1-\varepsilon)\ln n$, where $n$ is the number of points of the instance (for instances with sufficiently many points). Then
--
--   $$\mathrm{NP}\ \subseteq\ \mathrm{TIME}\big(n^{O(\log\log n)}\big),$$
--
--   that is, for every finite nonempty alphabet every NP language is decided by a deterministic one-tape Turing machine within $|w|^{c(\log_2\log_2|w|+1)}+c$ steps for some constant $c$.
--
--   This is the paper's main theorem: together with the greedy algorithm's $\ln n$ upper bound, it shows that $\ln n$ is the threshold of approximability of set cover, unless NP has slightly superpolynomial deterministic algorithms.
--
--   **Formalization Note** The approximation hypothesis is in value form (the algorithm outputs a number $v$ with $\mathrm{OPT}\le v\le(1-\varepsilon)\ln n\cdot\mathrm{OPT}$ on coverable instances with $n\ge n_0$), which is weaker than outputting a cover. Inside Section 4 the paper writes $N$ for the number of points; the theorem's $n$ is that number, not the number of variables of the formula. The choice of $k$, $\ell$, $m$ is the proof's and does not appear in the statement.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 647, Theorem 4.4

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Instance

namespace SetCoverThreshold.SetCover

theorem set_cover_threshold (h211 : Thm211) (hRaz : RazRepetition)
    (hNaor : NaorPartitionSystems) (ε : ℝ) (hε : 0 < ε)
    (hA : ApproximableWithin (fun n => (1 - ε) * Real.log n)) :
    ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym], CookPvsNP.NP Sym ⊆ LogLogTime Sym := by sorry

end SetCoverThreshold.SetCover
