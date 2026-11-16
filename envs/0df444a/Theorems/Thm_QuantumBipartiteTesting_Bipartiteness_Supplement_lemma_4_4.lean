-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_Supplement_lemma_4_4
-- name    : QuantumBipartiteTesting.Bipartiteness.Supplement.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:14:03.369206+00:00
-- url     : https://prove2.me/theorems/850df078-d48a-4cf0-98dd-a2d342bab6c5
-- title:
--   Lemma 4.4 — Simple cubic cloud expanders on every sufficiently large even order
-- statement:
--   There is an absolute $h_0>0$ and an order threshold $c_0$ such that every even $c\ge c_0$ admits a simple graph $J$ on $c$ vertices, every vertex of which has degree exactly three, satisfying
--   $$|e_J(U,U^c)|\ge h_0\min\{|U|,c-|U|\}\quad\text{for every }U\subseteq[c].$$
--   The constant precedes the order and graph. Empty and full cuts are included. These graphs provide the fixed clouds of the replacement construction.
--
--   Differences from the source:
--   - encoding: simple 3-regular graphs on [n] → oriented unordered edge pairs on Fin n, degree exactly three; reason: the published graph encoding counts each edge once and includes every simple graph
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Lemma 4.4, printed page = PDF page 23

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset

theorem lemma_4_4 :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ c₀ : ℕ, ∀ c ≥ c₀, Even c →
      ∃ J : Finset (Edge c), Cloud h₀ J := by sorry

end QuantumBipartiteTesting.Bipartiteness.Supplement
