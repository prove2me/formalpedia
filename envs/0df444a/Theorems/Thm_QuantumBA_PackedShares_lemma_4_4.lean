-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_4_4
-- name    : QuantumBA.PackedShares.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:48.490279+00:00
-- url     : https://prove2.me/theorems/41e82242-3d59-4a35-b036-4250a592c109
-- title:
--   Lemma 4.4 — public committee assignments with few overloaded committees and bounded memberships exist
-- statement:
--   Let $0<\varepsilon<1/3$, $t\le(1/3-\varepsilon)n$, $\beta\in(0,1]$ and $\gamma=1/3-\varepsilon/2$. Consider a level with $m$ nodes and committee size $k\le n$, where $k=n$ or
--   $$k\ge K(m):=\frac{2}{\varepsilon^2}\Bigl(\frac{n\ln2+2}{\max\{1,\beta m\}}+\ln\frac e\beta\Bigr).$$
--   There is an assignment of committees of size $k$ to the level's nodes such that, for every $F\subseteq P$ with $|F|\le t$, at most $\beta m$ committees $C$ have $|C\cap F|>\gamma|C|$, and every process lies in at most $\Delta=\lceil\max\{2emk/n,3L\}\rceil$ of the level's committees.
--
--   The algorithm uses the first such assignment in a fixed public order; the first property bounds the overloaded committees for every fault set the adversary may choose after seeing the assignment.
--
--   Differences from the source:
--   - reading: a level with committee size k (committees are subsets of P) → k ≤ n is a hypothesis; reason: committees are subsets of P = [n]; without it no k-subsets exist
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 20, Lemma 4.4 (PDF p. 21); proof §C.2, pp. 37–38 (PDF 38–39)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Tables

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 4.4 (committees). -/
theorem lemma_4_4 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 3) (n t : ℕ) (ht : (t : ℝ) ≤ (1 / 3 - ε) * n)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (m k : ℕ) (hkn : k ≤ n)
    (hk : k = n ∨ Kbound ε β n m ≤ k) :
    ∃ C : Fin m → Finset (Fin n), CommitteeProps ε β n t m k C := by sorry

end QuantumBA.PackedShares
