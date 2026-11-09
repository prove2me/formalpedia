-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_lemma_2_1
-- name    : ParityBarrier563.Trilinear.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:26.75488+00:00
-- url     : https://prove2.me/theorems/33a64a68-812e-47c9-ba97-731abf17e2eb
-- title:
--   Lemma 2.1 — Håstad's switching lemma: H_ρ is a k′-CNF and a k′-DNF with at most 2^{k′} clauses and terms except with probability (5pk)^{k′}
-- statement:
--   Let $V$ be a finite set of variables, let $k\ge0$ and $k'\ge1$ be integers, let $0<p\le1$, and let $H$ be a $k$-CNF or a $k$-DNF on $\{0,1\}^V$. For a $p$-random restriction $\rho$ of $V$,
--
--   $$\Pr_\rho\Bigl[\,H_\rho\text{ is not both a }k'\text{-CNF with at most }2^{k'}\text{ clauses and a }k'\text{-DNF with at most }2^{k'}\text{ terms}\Bigr]\le(5pk)^{k'}.$$
--
--   This is Håstad's switching lemma in the form used by the paper; applied layer by layer it gives the depth reduction of Lemma 2.2.
--
--   Differences from the source:
--   - encoding: probability over a p-random restriction → the finite sum of the explicit product weights of §2 over all restrictions; reason: the law has finite support; this is the same distribution
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Lemma 2.1, printed p.10 (PDF p.12); cited from [Hås89] and [O'D14, §4.4], no proof printed

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_CNF
import Definitions.Def_ParityBarrier563_Trilinear_Restriction

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Lemma 2.1 (Håstad's switching lemma), printed p.10 / PDF 12. -/
theorem lemma_2_1 (V : Type) [Fintype V] [DecidableEq V] (k k' : ℕ) (p : ℝ) (H : BoolFn V)
    (hk' : 1 ≤ k') (hp0 : 0 < p) (hp1 : p ≤ 1) (hH : IsCNF k H ∨ IsDNF k H) :
    restrProb p (fun ρ => ¬ (IsCNFWith k' ((2 ^ k' : ℕ) : ℕ∞) (restrict ρ H) ∧
        IsDNFWith k' ((2 ^ k' : ℕ) : ℕ∞) (restrict ρ H))) ≤
      (5 * p * k) ^ k' := by sorry

end ParityBarrier563.Trilinear
