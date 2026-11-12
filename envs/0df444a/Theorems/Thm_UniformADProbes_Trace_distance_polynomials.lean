-- Prove2me | Theorems.Thm_UniformADProbes_Trace_distance_polynomials
-- name    : UniformADProbes.Trace.distance_polynomials
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:00.144138+00:00
-- url     : https://prove2.me/theorems/ba13d6ac-dc38-4c05-a7f8-393baaab0752
-- title:
--   Section 3, equation (9) — Distance polynomials and the all-ones matrix
-- statement:
--   Let $T$ be a finite nonempty connected simple tree on $n$ vertices, with adjacency matrix $A_T$ and diagonal degree matrix $D_T$. Use the defined recurrence $P_0=1$, $P_1=x$, $P_2=x^2-y$, $P_k=xP_{k-1}-(y-1)P_{k-2}$ for $k\ge3$. For every integer $k\ge0$ and vertices $u,v$,
--   $$P_k(A_T,D_T)_{uv}=\mathbf1_{\{\operatorname{dist}_T(u,v)=k\}}.$$
--   Consequently, for every $N\ge n$, with $J_N=\sum_{k<N}P_k$,
--   $$J_N(A_T,D_T)=\mathbf1\mathbf1^T,\qquad
--   \operatorname{tr}(J_N(A_T,D_T)X)=\mathbf1^TX\mathbf1$$
--   for every real $n\times n$ matrix $X$.
--
--   Both distance counting and the all-ones identity are retained. This supplies the conversion between pointed Gram entries and traces without adding an all-ones matrix as a circuit input. The singleton tree is included.
--
--   Differences from the source:
--   - encoding: distance indicators and their all-ones sum on finite trees → integer matrix evaluation on Fin n, followed by real evaluation for the arbitrary real test matrix; reason: distance and integer indicators are exact, and casting the integer polynomial preserves the real trace identity
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), §3 equations (8)–(9) and their immediately preceding distance-counting argument, p. 8 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false

namespace UniformADProbes.Trace

theorem distance_polynomials (n : ℕ)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    (∀ k : ℕ, ∀ i j : Fin n,
      polyEval (adjacency T) (degreeMatrix T) (distancePoly k) i j =
        if T.dist i j = k then (1 : ℤ) else 0) ∧
    (∀ N : ℕ, n ≤ N →
      polyEval (adjacency T) (degreeMatrix T) (distanceSum N) =
        (fun _ _ => (1 : ℤ))) ∧
    (∀ N : ℕ, n ≤ N → ∀ X : Matrix (Fin n) (Fin n) ℝ,
      Matrix.trace (polyEval (realMatrix (adjacency T)) (realMatrix (degreeMatrix T))
        (distanceSum N) * X) = dot (ones n) (X.mulVec (ones n))) := by sorry

end UniformADProbes.Trace
