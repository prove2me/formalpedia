-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_lemma_2_2
-- name    : ParityBarrier563.Trilinear.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:22.737807+00:00
-- url     : https://prove2.me/theorems/23c61391-253f-4596-b2fe-243279c626de
-- title:
--   Lemma 2.2 — Håstad's depth reduction: after a q-random restriction a depth-d circuit with an OR output is an OR of s^{O(1)} k-CNFs with probability 3/4
-- statement:
--   Let $d\ge3$ be a fixed integer. There exist numbers $k(s)$ and $q(s)$, depending only on $d$ and $s$, and an exponent $A$ depending only on $d$, with the following properties (the depth-reduction witness property):
--
--   1. $0<q(s)\le1$, $k(s)=\Theta_d(\log s)$ and $1/q(s)=\Theta_d(\log^{d-3}s)$ for all $s\ge2$;
--   2. for every $s\ge2$, every set $V$ of variables with $2\le|V|\le s$, and every function $F:\{0,1\}^V\to\{0,1\}$ computed by a depth-$d$ circuit with at most $s$ gates and an OR output gate, a $q(s)$-random restriction $\varphi$ of $V$ satisfies
--   $$\Pr_\varphi\bigl[F_\varphi\text{ is the OR of at most }s^{A}\ k(s)\text{-CNFs}\bigr]\ge\frac34 .$$
--
--   This is the step that reduces every constant depth to depth three; Lemma 5.1 uses exactly these numbers.
--
--   Differences from the source:
--   - generalization: there are numbers k and q (after V and s are fixed) → k(s), q(s) and A chosen once for each d, as functions of s alone, before V and the circuit; reason: choosing them independently of V covers the printed order of quantifiers, and the paper's own parallel construction (proof of Lemma 6.2, printed p.26) builds k and q from d and s only
--   - encoding: k = Θ_d(log s), 1/q = Θ_d(log^{d−3} s), s^{O_d(1)} → two-sided bounds with positive constants valid for every s ≥ 2, and a real exponent A, all existentially quantified once for each d; reason: this is the meaning of the Θ_d and O_d notation; log₂ s ≥ 1 for s ≥ 2
--   - encoding: a size bound s ≥ |V| → a natural number s; reason: a circuit has at most s gates iff it has at most ⌊s⌋ gates, and |V| ≤ s iff |V| ≤ ⌊s⌋
--   - generalization: OR-output circuits reading literals and constants → OR-output circuits also allowing empty fan-in gates; reason: an empty AND is true and an empty OR is false; this adds circuits and includes every source circuit with the same gate count and depth
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Lemma 2.2, printed p.10 (PDF p.12); cited from [Hås89] and [O'D14, §4.4], no proof printed

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_DepthReductionWitness

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Lemma 2.2 (Håstad's depth reduction), printed p.10 / PDF 12. -/
theorem lemma_2_2 (d : ℕ) (hd : 3 ≤ d) :
    ∃ (k : ℕ → ℕ) (q : ℕ → ℝ) (A : ℝ), DepthReductionWitness d k q A := by sorry

end ParityBarrier563.Trilinear
