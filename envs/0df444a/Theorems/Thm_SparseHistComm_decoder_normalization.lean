-- Prove2me | Theorems.Thm_SparseHistComm_decoder_normalization
-- name    : SparseHistComm.decoder_normalization
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:26.588858+00:00
-- url     : https://prove2.me/theorems/59e7689a-bd9e-4108-b671-645a1c6495e1
-- title:
--   Proof of Lemma 2 — decoder normalization: $N(v) \ge 0$, $\|N(v)\|_1 \le k + D$, accuracy preserved
-- statement:
--   Let $n \ge 1$, $1 \le k \le d$, $d \ge 2$ and $0 \le D < k$. For a decoder output $v \in \mathbb R^d$ let $N(v)$ be its normalization: clip each coordinate to $[0,1]$, and replace the result by $0$ if its $\ell_1$ norm exceeds $k + D$. Then
--
--   1. $N(v) \ge 0$ coordinatewise and $\|N(v)\|_1 \le k + D$;
--   2. for every admissible input profile ($\|x_i\|_0 \le k$) with empirical histogram $u$, clipping does not increase the distance: $\|\mathrm{clip}(v) - u\|_1 \le \|v - u\|_1$;
--   3. for every such $u$, $\|v - u\|_1 \le D$ implies $\|N(v) - u\|_1 \le D$.
--
--   So a protocol's decoder may be replaced by $N \circ \hat u$ without changing its communication cost or reducing its accuracy, and one may assume $\hat u \ge 0$, $\|\hat u\|_1 \le k + D$ on every outcome. This is the first step of the proof of Lemma 2.
--
--   Differences from the source:
--   - encoding: binary vectors xᵢ ∈ {0,1}^d with ‖xᵢ‖₀ ≤ k → supports xᵢ : Finset (Fin d) with card ≤ k; reason: bijection, ‖xᵢ‖₀ = card
--   - encoding: we may modify the decoder without changing its cost or reducing its accuracy → pointwise properties of the explicit map N = normalize k D on decoder outputs; reason: the modified protocol keeps every channel (same cost) and clause 3 gives the success-event inclusion; same content
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A (proof of Lemma 2), p.14

import Mathlib
import Definitions.Def_SparseHistComm_Admissible
import Definitions.Def_SparseHistComm_empHist
import Definitions.Def_SparseHistComm_l1
import Definitions.Def_SparseHistComm_clip
import Definitions.Def_SparseHistComm_normalize

namespace SparseHistComm

/-- **Proof of Lemma 2, decoder normalization** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A, p.14). Clip a decoder output
`v` to `[0, 1]` coordinatewise; if the clipped output has `ℓ₁` norm greater than `k + D`, replace
it by zero. The result `N(v)` satisfies `N(v) ≥ 0` and `‖N(v)‖₁ ≤ k + D`; clipping cannot increase
the distance to any admissible histogram `u`; and `‖v − u‖₁ ≤ D` implies `‖N(v) − u‖₁ ≤ D`.

**Formalization Note** Stated for the explicit map `normalize k D`; replacing a protocol's decoder
by `normalize k D ∘ dec` keeps its channels (hence its cost) and, by the last clause, does not
reduce its success probability. -/
theorem decoder_normalization (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (D : ℝ) (hD0 : 0 ≤ D) (hDk : D < k) (v : Fin d → ℝ) :
    (∀ a, 0 ≤ normalize k D v a) ∧ ∑ a, |normalize k D v a| ≤ k + D ∧
    ∀ x : Fin n → Finset (Fin d), Admissible k x →
      l1 (clip v) (empHist x) ≤ l1 v (empHist x) ∧
      (l1 v (empHist x) ≤ D → l1 (normalize k D v) (empHist x) ≤ D) := by sorry

end SparseHistComm
