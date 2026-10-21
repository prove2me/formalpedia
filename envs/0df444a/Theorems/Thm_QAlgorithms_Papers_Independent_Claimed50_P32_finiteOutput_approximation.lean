-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P32_finiteOutput_approximation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P32.finiteOutput_approximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:25:43.672015+00:00
-- url     : https://prove2.me/theorems/ef700a48-dc36-49f7-a062-bc6e18d228cd
-- title:
--   Finite-output compressions approximate every channel strongly
-- statement:
--   Let $\Phi$ be any channel between nonzero separable complex Hilbert spaces. Let $(P_n)$ be arbitrary finite-rank orthogonal projections on the output space, increasing strongly to the identity. Define $\Phi_n(X)=P_n\Phi(X)P_n$ for every trace-class operator $X$. Then each $\Phi_n$ is a quantum operation, every output is supported on $\operatorname{ran}P_n$, and
--
--   $$\Phi_n\longrightarrow\Phi\quad\text{pointwise in trace norm on every input state}.$$
--
--   The output ranks may stabilize in finite dimensions. This supplies the paper's finite-output approximation.
--
--   **Formalization Note** Each projection is represented by a finite orthonormal range basis, with arbitrary rank at each index. The theorem asserts existence of operations with the exact compression formula and the support identity $P_n\Phi_n(X)P_n=\Phi_n(X)$.
-- source:
--   On approximation of quantum channels, arXiv:0711.2245v1, PDF p. 7, §3, unnumbered: compression approximation of every channel

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P32

noncomputable section

open Filter

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P32

open QAlgorithms.RealRegisters (Hilbert)

/-- §3, PDF p.7: compressions by arbitrary increasing finite-rank projections
converging strongly to the identity are operations, have the claimed finite output
support, and converge strongly to the original channel. Ranks may be zero or
become constant in finite dimensions. -/
theorem finiteOutput_approximation {I J : Type}
    [Countable I] [Nonempty I] [Countable J] [Nonempty J] (Phi : StrongChannel I J)
    (rank : ℕ → ℕ) (v : (n : ℕ) → Fin (rank n) → Hilbert J)
    (horth : ∀ n, Orthonormal ℂ (v n))
    (hincreasing : ∀ n u,
      finiteProjection (v (n + 1)) (finiteProjection (v n) u) = finiteProjection (v n) u)
    (hidentity : ∀ u : Hilbert J,
      Tendsto (fun n => finiteProjection (v n) u) atTop (nhds u)) :
    ∃ approx : ℕ → CanonicalOperation I J,
      (∀ n (X : TraceOperator I),
        (approx n).act X.val = finiteCompression (v n)
          ⟨Phi.val.act X.val, Phi.val.operation.1 X.val X.property⟩) ∧
      (∀ n (X : TraceOperator I),
        finiteCompression (v n)
          ⟨(approx n).act X.val, (approx n).operation.1 X.val X.property⟩ =
          (approx n).act X.val) ∧
      Tendsto approx atTop (nhds Phi.val) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P32

end
