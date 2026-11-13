-- Prove2me | Theorems.Thm_PPADSIS_SubexpSIS_searchRTC_polyTime
-- name    : PPADSIS.SubexpSIS.searchRTC_polyTime
-- status  : Open
-- author  : @arka
-- created : 2026-11-13T05:39:30.832201+00:00
-- url     : https://prove2.me/theorems/e14f4c05-69cf-43b8-acf9-a6911b61027b
-- title:
--   Lemma 3.9 (efficiency half) — the exhaustive-search tree circuit is computable in polynomial time
-- statement:
--   Let $\Phi$ be the exhaustive-search tree circuit map `PPADSIS_SubexpSIS_SearchRTC`, which sends a Boolean circuit $\varphi$ to a regular tree circuit $\Phi(\varphi)$. The map
--   $$\langle\varphi\rangle\ \longmapsto\ \langle\Phi(\varphi)\rangle$$
--   from the description of a circuit to the description of its tree circuit is computable in polynomial time: one multi-stack Turing machine (Mathlib's `FinTM2` model, as in the published `PolyTimeComputable`) maps the code of every circuit $\varphi$ to the code of $\Phi(\varphi)$ within a number of steps polynomial in the length of the input code.
--
--   This is the efficiency half of Lemma 3.9 ("computed from $\varphi$ in polynomial time"). The construction is syntactic: $\Phi(\varphi)$ copies the gates of $\varphi$, appends $n$ conjunctions, and repeats one fixed combining circuit with $2n+2$ gates $n$ times, so its description has length polynomial in that of $\varphi$. Together with `PPADSIS.SubexpSIS.searchRTC_spec` it gives the milestone `PPADSIS.SubexpSIS.lemma_3_9`.
--
--   **Formalization Note** Polynomial time is `PPSLattice.PolyTimeOn Circuit.enc (fun φ => (searchRTC φ).enc)`: it is required on every circuit, well formed or not, with descriptions `Circuit.enc` and `RTC.enc`.
-- source:
--   Arka Rai Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript), Lemma 3.9, p. 22 (with Definition 3.8, p. 22)

import Mathlib
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_PPADSIS_SubexpSIS_SearchRTC

namespace PPADSIS.SubexpSIS

theorem searchRTC_polyTime : PPSLattice.PolyTimeOn Circuit.enc (fun φ => (searchRTC φ).enc) := by sorry

end PPADSIS.SubexpSIS
