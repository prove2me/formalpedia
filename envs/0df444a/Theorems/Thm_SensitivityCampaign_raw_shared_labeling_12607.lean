-- Prove2me | Theorems.Thm_SensitivityCampaign_raw_shared_labeling_12607
-- name    : SensitivityCampaign.raw_shared_labeling_12607
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-20T06:30:46.107071+00:00
-- url     : https://prove2.me/theorems/7ab29971-4da0-4191-bfbe-232def34f6ad
-- title:
--   A shared tournament labeling with five simultaneous defect bounds
-- statement:
--   Every tournament on $12607$ vertices admits one binary labeling of its directed edges with the following five simultaneous properties. Set
--
--   $$s_0=23,\quad s_1=33,\quad s_2=45,\quad s_3=57,\quad s_4=71.$$
--
--   For each $q\in\{0,1,2,3,4\}$, each vertex subset $I$, and each assignment of a binary target color $c_j$ to every vertex, if every $i\in I$ has at most $q$ outgoing arcs $i\to j$ within $I$ whose labels differ from $c_j$, then
--
--   $$|I|<s_q.$$
--
--   A tournament here is a loopless directed graph in which exactly one of the two possible arcs joins each distinct vertex pair. One labeling must satisfy every listed tolerance, subset, and target-color assignment at once. The labeling is represented on all ordered vertex pairs; values on pairs that are not arcs are unused. The statement has no unproved probability or local-lemma hypothesis.
-- source:
--   Self-contained formal proof and application of the classical finite asymmetric Lovász local lemma, developed for yousofy with Codex (2026-10-20). The five tolerances, q-tag encoding, exact dependency counts and rational activity certificate are extracted from the kernel-checked four-stage finite-family construction, sourceSHAa21a28f77e379ef6c0f691cd75ee5888042027181654eb57804202caa3393d79. Classical asymmetric local lemma: Moser and Tardos, A constructive proof of the general Lovász Local Lemma, arXiv:0903.0544v3, Theorem1.1 (attributing Erdős and Lovász1975), https://arxiv.org/abs/0903.0544. Retains tournament/labeling definitions and counting provenance from Robin Kothari and Codex, accepted2.075 foundation, https://prove2.me/theorems/49fdd176-c319-4f1e-b15f-b1fd5130f0bc, submission819ad4c6-aa25-48ca-82e9-c8df39c182c0, including its earlier OpenAI and community attribution.

import Mathlib
open scoped Classical

theorem SensitivityCampaign.raw_shared_labeling_12607 (A : Fin 12607 → Fin 12607 → Prop)
    (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i)) :
    ∃ label : Fin 12607 → Fin 12607 → Fin 2,
      ∀ q : Fin 5, ∀ I : Finset (Fin 12607),
        ∀ colors : Fin 12607 → Fin 2,
        (∀ i ∈ I, (I.filter (fun j => A i j ∧ label i j ≠ colors j)).card ≤ q.val) →
          I.card < (![23,33,45,57,71] q) := by sorry
