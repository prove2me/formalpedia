-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_5_3
-- name    : QuantumBA.PackedShares.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:48.27882+00:00
-- url     : https://prove2.me/theorems/fb829197-002e-4c74-a0a5-69ca21ef230a
-- title:
--   Lemma 5.3 — forwarding graphs with out-degree D, column degree ≤ J_graph and sampler property (10) exist
-- statement:
--   Let $\rho\in(0,1/2]$, let $U,V$ be committees of sizes $k\le k'$ (subsets of $P=[n]$, so $k'\le n$), and let $D\le k'$ be an integer with $D=k'$ or $2D\rho^3k\ge(k+k')\ln2+\ln8$. Then there is a bipartite graph between the rows $U$ and the columns $V$ such that (i) every row has $D$ distinct neighbours, (ii) every column has degree at most $J_{\mathrm{graph}}=\lceil\max\{2ekD/k',3L\}\rceil$ (or $k$ if $D=k'$), with $L=\lceil\log_2n\rceil$, and (iii) for every $Z\subseteq V$
--   $$\#\Bigl\{u\in U:\frac{|N(u)\cap Z|}{D}>\frac{|Z|}{k'}+\rho\Bigr\}\le\rho k. \tag{10}$$
--
--   The graphs fixed by exhaustive search from this lemma carry the transfers of Algorithm 2; property (10) drives the protection argument of Lemma 5.4.
--
--   Differences from the source:
--   - encoding: committees U, V of sizes k ≤ k′ (sets of processes) → rows Fin k and columns Fin k′ (positions in the committees), with k′ ≤ n stated explicitly; reason: the properties do not depend on the names of the processes; committees are subsets of P, so k′ ≤ n
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 29, Lemma 5.3 (PDF p. 30); proof §C.3, p. 38 (PDF 39)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Tables

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 5.3 (forwarding graphs). -/
theorem lemma_5_3 (n : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (k k' D : ℕ) (hkk' : k ≤ k')
    (hk'n : k' ≤ n) (hD : D ≤ k')
    (hDcond : D = k' ∨ (k + k' : ℝ) * Real.log 2 + Real.log 8 ≤ 2 * D * ρ ^ 3 * k) :
    ∃ N : Fin k → Finset (Fin k'), GraphProps ρ n k k' D N := by sorry

end QuantumBA.PackedShares
