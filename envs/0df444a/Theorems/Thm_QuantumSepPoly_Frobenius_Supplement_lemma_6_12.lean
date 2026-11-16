-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_Supplement_lemma_6_12
-- name    : QuantumSepPoly.Frobenius.Supplement.lemma_6_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:56:15.615813+00:00
-- url     : https://prove2.me/theorems/adce0c2b-06f9-484e-a787-ca9da0590c9c
-- title:
--   Lemma 6.12 — Individual-register product acceptance bound
-- statement:
--   Let $N,A,\delta\ge1$, $0<\xi\le1$, and let $I$ be any sparse Boolean two-CSP with alphabet size $A$, distinct endpoints, no repeated unordered edge and vertex degrees in $[1,\delta]$. Suppose $\operatorname{OPT}(I)\le1-\xi$ and integer $k\ge\max(64A,\sqrt N)$. Every product $x=x_1\otimes\cdots\otimes x_k$ of unit vectors in $\mathbb C^N\otimes\mathbb C^A$ satisfies
--   $$\frac12 x^*(M_c+M_u)x\le1-\frac{\xi^2}{2^{45}A^6\delta^4}.$$
--   The product condition is across individual registers. There is no completeness assumption and no upper bound on $k$.
--
--   Differences from the source:
--   - encoding: finite complex registers with one-based indices → zero-based finite function registers and explicit mixed-radix basis maps; reason: bijections preserve the source matrices and the specified bipartite cut
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 6.12, p. 32 (PDF p. 32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Registers

open scoped BigOperators ENNReal

namespace QuantumSepPoly.Frobenius.Supplement

theorem lemma_6_12 (N A δ k : ℕ) (ξ : ℝ) (I : MaxCSP N 2 (Fin A))
    (hN : 1 ≤ N) (hA : 1 ≤ A) (hδ : 1 ≤ δ) (hξ : 0 < ξ ∧ ξ ≤ 1)
    (hI : Sparse I δ) (hopt : cspOPT I ≤ 1-ξ)
    (hk : max (64*(A : ℝ)) (Real.sqrt N) ≤ k)
    (x : Fin k → Register N A → ℂ) (hx : ∀ l, ∑ i, ‖x l i‖^2 = 1) :
    quadratic (consistency I k + uniformity N A k) (registerProduct x) / 2 ≤
      1-ξ^2/(2^45*(A : ℝ)^6*(δ : ℝ)^4) := by sorry

end QuantumSepPoly.Frobenius.Supplement
