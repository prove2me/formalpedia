-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_pointer_endpoint_public_upper
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.pointer_endpoint_public_upper
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:00:09.592816+00:00
-- url     : https://prove2.me/theorems/ff259d9d-92c7-4059-b37f-3e57cc8ffc83
-- title:
--   Public-coin pointer-endpoint upper bound
-- statement:
--   For $n\ge2$ and $k\ge1$, let $g_k$ be the vertex reached after $k+1$ alternating applications of unrestricted pointer maps, beginning at a fixed Alice vertex $v_1$. Messages alternate starting with Bob, and the final receiver may locally announce the endpoint without a further charged message. Use public randomness independent of both inputs, and require success at least $1-\varepsilon$ on every pair of maps, where $0<\varepsilon<1$.
--
--   There are absolute constants $C>0,n_0\ge2$, chosen before all these parameters, such that for $n\ge n_0$ a protocol with at most $k$ messages has worst-case bit cost $c$ satisfying
--   $$
--   c\le C\left[\frac{n}{k\varepsilon}\left(L_{\lfloor k/2\rfloor}(n)+\log_2 k\right)+k\log_2 n\right].
--   $$
--   Here $L_0(n)=\max\{1,n\}$ and $L_{j+1}(n)=\max\{1,\log_2 L_j(n)\}$: the superscript denotes iteration, and precision saturates at one bit.
--
--   This is the stronger vertex-valued bound, rather than a bound only for pointer parity. Integer round-pair and bit-rounding conventions are absorbed in the absolute constant.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 13, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Theorem 2, PDF p.13: public-coin endpoint bound, floor(k/2) iterates and one-bit saturation.
Odd k extends the preceding even case by one pointer message; k=1 can send the full table. -/
theorem pointer_endpoint_public_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∀ (k n : ℕ), 0 < k → n0 ≤ n → ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∀ v1 : Fin n, ∃ (c : ℕ) (P : PublicProtocol (PointerMap n) (PointerMap n) (Vertex n)),
        P.bounded .bob k c ∧ P.computes (endpoint k v1) eps ∧
        (c : ℝ) ≤ C * ((n : ℝ) / ((k : ℝ) * eps) *
          (iteratedLog (k / 2) n + Real.logb 2 k) + k * Real.logb 2 n) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
