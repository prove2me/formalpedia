-- Prove2me | Theorems.Thm_PhaseEncodedQGE_Supplement_theorem_B_22
-- name    : PhaseEncodedQGE.Supplement.theorem_B_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:34:45.168506+00:00
-- url     : https://prove2.me/theorems/0c16a8a9-b058-4ff8-8910-882e0d50db32
-- title:
--   Theorem B.22 — Hadamard vanishing: $F_{0,k}=0$ under $|\chi(\pi/2,0)\rangle$
-- statement:
--   Let $|\chi(\theta,\varphi)\rangle=\cos(\theta/2)|0\rangle+e^{i\varphi}\sin(\theta/2)|1\rangle$, so that $|\chi(\pi/2,0)\rangle=|+\rangle$ is the Hadamard preparation. For the preparation $|\chi(\pi/2,0)\rangle$ the nonadjacent pair kernel vanishes identically:
--   $$F_{0,k}=0\qquad\text{for every codegree }k\in\{0,1,2,3\}\text{ and every }\gamma.$$
--   Equivalently, the pair kernel (53) of every nonadjacent pair of vertices of a cubic graph vanishes under the Hadamard preparation.
--
--   This is why the Hadamard-prepared purity closure of Theorem 6.1 contains no $C_3$ and no $C_4$ term: the nonadjacent pairs contribute nothing at second order.
--
--   **Formalization Note** Stated for the mission's class kernels $F_{0,k}$ (every $n$) and, per pair, for every nonadjacent pair $i\ne j$ of every cubic graph.
--
--   Differences from the source:
--   - encoding: "the nonadjacent pair kernel vanishes identically: $F_{0,k}=0$" → both $F_{0,k}=0$ for the class kernels ($k\le3$, every $n$) and, per pair, kernel $(i,j)=0$ for every nonadjacent $i\ne j$ of every cubic graph; reason: on cubic graphs the class kernel equals the kernel of every pair of its class, so the two forms state the same fact
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. B.2.6, p.33 (PDF p.34), Theorem B.22; kernel (53), p.30 (PDF p.31); preparation (72)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
import Definitions.Def_PhaseEncodedQGE_Supplement_Purity
set_option autoImplicit false

namespace PhaseEncodedQGE.Supplement

/-- Theorem B.22, Hadamard vanishing (Miller, Lee, *Structural Accessibility in Phase-Encoded
Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. B.2.6, p.33).

For the preparation `|χ(π/2, 0)⟩` the nonadjacent pair kernel vanishes identically: `F_{0,k} = 0`
for every codegree `k` and every `γ`.

**Formalization Note** Stated twice: for the class kernels, `classKernel (π/2) 0 γ n 0 k = 0` for
every `n`, every `γ` and every codegree `k ∈ {0, 1, 2, 3}` (the motif-based `F_{0,k}` of the
mission); and per pair, the kernel (53) under `|χ(π/2, 0)⟩^{⊗n}` (base `chiPrep n (π/2) 0`, the
Hadamard preparation) of every nonadjacent pair `i ≠ j` of every cubic graph on `Fin n` is `0`,
whatever its codegree. The `X` mixer with one repetition is implicit in the kernel (53). -/
theorem theorem_B_22 :
    (∀ (n k : ℕ) (γ : ℝ), k ≤ 3 → classKernel (Real.pi / 2) 0 γ n 0 k = 0) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (γ : ℝ) (i j : Fin n), i ≠ j →
      ¬ G.Adj i j → pairKernel (chiPrep n (Real.pi / 2) 0) G γ i j = 0) := by sorry

end PhaseEncodedQGE.Supplement
