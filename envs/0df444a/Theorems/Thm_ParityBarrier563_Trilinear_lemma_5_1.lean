-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_lemma_5_1
-- name    : ParityBarrier563.Trilinear.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:45.388859+00:00
-- url     : https://prove2.me/theorems/37decd92-b665-4625-8f3f-d0d554129b01
-- title:
--   Lemma 5.1 — if E_φ corr_k(g_φ) ≤ ε for Lemma 2.2's k and q, every depth-d circuit with s gates has ε ≥ s^{−O(1)}
-- statement:
--   Let $d\ge3$, and let $k(s),q(s),A$ be numbers with the properties given by Lemma 2.2 (a depth-reduction witness for depth $d$). There is a constant $B>0$, depending only on these numbers, such that the following holds. Let $V$ be a set of variables and $s\ge|V|\ge2$. Let $F:\{0,1\}^V\to\{0,1\}$ be a function whose sign $g=2F-1$ satisfies
--
--   $$\mathbb E_\varphi\,\mathrm{corr}_{k(s)}(g_\varphi)\le\varepsilon,$$
--
--   where $\varphi$ is a $q(s)$-random restriction of $V$. If some depth-$d$ circuit with at most $s$ gates computes $F$ (with either output type), then
--
--   $$\varepsilon\ge s^{-B}.$$
--
--   This is the covering argument that converts small correlation of restrictions with $k$-CNFs into a circuit lower bound.
--
--   Differences from the source:
--   - generalization: k and q the numbers given by Lemma 2.2 → any (k, q, A) with the depth-reduction witness property, with B chosen after them and before V, s, F, ε and the circuit; reason: the numbers Lemma 2.2 provides are such a witness, so the statement specializes to the source's; Lemma 2.2 shows witnesses exist, so it is not vacuous
--   - encoding: ε ≥ s^{−O(1)} → ∃ B > 0 with s^{−B} ≤ ε; reason: the meaning of the O-notation, with a constant independent of V, s and the circuit
--   - encoding: a size bound s ≥ |V| → a natural number s; reason: a circuit has at most s gates iff it has at most ⌊s⌋ gates, |V| ≤ s iff |V| ≤ ⌊s⌋, and ⌊s⌋^{−B} ≥ s^{−B}
--   - generalization: depth-d circuits of AND/OR gates reading literals and constants, with the output an AND or OR gate → circuits whose output may be any node (a gate, a literal or a constant) and whose gates may have fan-in zero; reason: these only add circuits: every circuit of the source is one of them with the same size and depth, so the Lean statement specializes to the source's
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Lemma 5.1, printed p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Correlation
import Definitions.Def_ParityBarrier563_Trilinear_DepthReductionWitness

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Lemma 5.1, printed p.16 / PDF 18. `k = k(s)` and `q = q(s)` are any numbers with the
properties given by Lemma 2.2 (`DepthReductionWitness`); the exponent `B` depends only on them. -/
theorem lemma_5_1 (d : ℕ) (hd : 3 ≤ d) (k : ℕ → ℕ) (q : ℕ → ℝ) (A : ℝ)
    (hW : DepthReductionWitness d k q A) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (s : ℕ) (F : BoolFn V) (ε : ℝ) (C : Circuit V),
        2 ≤ Fintype.card V → Fintype.card V ≤ s →
        restrExpect (q s) (fun φ => corr (k s) (restrict φ (sgn F))) ≤ ε →
        C.size ≤ s → C.depth ≤ d → C.Computes F →
        (s : ℝ) ^ (-B) ≤ ε := by sorry

end ParityBarrier563.Trilinear
