-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_Supplement_lemma_6_13
-- name    : QuantumSepPoly.Frobenius.Supplement.lemma_6_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:56:39.168593+00:00
-- url     : https://prove2.me/theorems/2873722c-aa06-4270-8a76-409980381776
-- title:
--   Lemma 6.13 — Under the same CSP and k conditions, h_Sep(M) ≤ 1−ξ⁴/(100·2^90|Ω|^12δ^8)
-- statement:
--   For every sparse Boolean two-CSP with positive size $N$, positive alphabet size $A$, degrees in $[1,\delta]$ with $\delta\ge1$, distinct endpoints and unique unordered edges, suppose $0<\xi\le1$, $\operatorname{OPT}(I)\le1-\xi$, and $k\ge\max(64A,\sqrt N)$. The explicitly constructed two-block acceptance operator satisfies
--   $$h_{\rm Sep}(M)\le1-\frac{\xi^4}{100\cdot2^{90}A^{12}\delta^8}.$$
--   The support is over the published separable states across the first and last $k$ registers, allowing entanglement within either block.
--
--   Differences from the source:
--   - encoding: finite complex registers with one-based indices → zero-based finite function registers and explicit mixed-radix basis maps; reason: bijections preserve the source matrices and the specified bipartite cut
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 6.13, p. 34 (PDF p. 34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Registers
import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Parameters

open scoped BigOperators ENNReal

namespace QuantumSepPoly.Frobenius.Supplement

theorem lemma_6_13 (N A δ k : ℕ) (ξ : ℝ) (I : MaxCSP N 2 (Fin A))
    (hN : 1 ≤ N) (hA : 1 ≤ A) (hδ : 1 ≤ δ) (hξ : 0 < ξ ∧ ξ ≤ 1)
    (hI : Sparse I δ) (hopt : cspOPT I ≤ 1-ξ)
    (hk : max (64*(A : ℝ)) (Real.sqrt N) ≤ k) :
    support (flatten (acceptance I k)) ≤ 1-blockGap A δ ξ := by sorry

end QuantumSepPoly.Frobenius.Supplement
