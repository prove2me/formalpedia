-- Prove2me | Theorems.Thm_UniformADProbes_Trace_uniform_spanning_probes
-- name    : UniformADProbes.Trace.uniform_spanning_probes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:55.850355+00:00
-- url     : https://prove2.me/theorems/e7ce08ae-4aef-44ef-b5e8-c77b4fa97aa2
-- title:
--   Theorem 1.2 — Uniform spanning probes, including resources
-- statement:
--   For each integer $N\ge1$, the defined constructor emits the same indexed probe family for all admissible inputs. Let $1\le n\le N$ and let $H,K\in M_n(\mathbb R)$ be symmetric with $\operatorname{diam}\operatorname{Spec}(K)\le N-1$. For every seed $v\in\mathbb R^n$, including zero,
--   $$\operatorname{span}_{\mathbb R}\{U_{i,j}(H,K)v:0\le j\le i<N\}=\mathcal M(H,K;v).$$
--   There are exactly $M=N(N+1)/2$ indexed members, even when their evaluations coincide. The shared emitted circuit is valid, its designated registers denote the prescribed polynomials and their adjoints, it has at most $100N^2$ stored instructions, and every register has formal degree at most $N-1$. Each prescribed scalar has at most $8\ell_N$ signed bits, where $\ell_N=\lceil\log_2(N+1)\rceil$.
--
--   The family spans arbitrary proper cyclic modules and requires no norm bound on $H$, integrality, or cyclicity of the seed. Its finite uniform size is the reusable input to pointed reconstruction.
--
--   **Formalization Note** The emitter uses twelve instructions per new triangular member and four initial instructions when $N\ge2$; its scalars have absolute value at most $N^3$. This gives the stated explicit envelopes. For $N=1$ it emits identity alone. There is no bit bound on arbitrary real evaluated entries.
--
--   Differences from the source:
--   - encoding: an indexed triangular family in finite real coordinates → a lexicographic list, matrix coordinates Fin n, and its designated forward and adjoint registers; reason: the list counts indexed members and uses the identical recurrence
--   - encoding: shared size O(N²), degree N − 1, and literal size O(log(N+1)) → 100N² instructions, every-register degree ≤ N−1, and 8 ceil(log₂(N+1)) signed bits; reason: the fixed emitter expands the same recurrence with twelve instructions per new member; the scalar bound is N³
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), Theorem 1.2 and its resource proof, p. 2, 6 (PDF p. 3, 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_circuits

set_option autoImplicit false

namespace UniformADProbes.Trace

theorem uniform_spanning_probes :
    ∀ N : ℕ, 1 ≤ N →
      let p := probeProgram N
      let C : Circuit := ⟨p.2.code, 0⟩
      C.Valid ∧
      (probeList N).length = N * (N + 1) / 2 ∧
      p.1.size = N * (N + 1) / 2 ∧
      C.code.size ≤ 100 * N^2 ∧
      C.DegreeBound (N - 1) ∧
      C.LiteralBound (8 * (Nat.clog 2 (N + 1))) ∧
      (∀ j : Fin p.1.size,
        (p.1[j]).1 < C.code.size ∧ (p.1[j]).2 < C.code.size ∧
        (registers C x y)[(p.1[j]).1]?.getD 0 = (probeList N)[j.val]?.getD 0 ∧
        (registers C x y)[(p.1[j]).2]?.getD 0 = adjoint ((probeList N)[j.val]?.getD 0)) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ H K : Matrix (Fin n) (Fin n) ℝ,
        H.IsSymm → K.IsSymm → spectralDiameter K ≤ (N : ℝ) - 1 →
        ∀ v : Fin n → ℝ, responseSpan H K v (probeList N) = cyclicModule H K v) := by sorry

end UniformADProbes.Trace
