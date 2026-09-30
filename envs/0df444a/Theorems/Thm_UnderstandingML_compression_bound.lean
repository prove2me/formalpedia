-- Prove2me | Theorems.Thm_UnderstandingML_compression_bound
-- name    : UnderstandingML.compression_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T06:00:30.439799+00:00
-- url     : https://prove2.me/theorems/d8f562ec-8514-427c-89f2-a068e4ab602a
-- title:
--   Theorem 30.2: if A(S) = B(z_{i₁},…,z_{i_k}) and m ≥ 2k, then w.p. ≥ 1−δ, L_D(A(S)) ≤ L_V(A(S)) + √(L_V(A(S)) 4k log(m/δ)/m) + 8k log(m/δ)/m
-- statement:
--   **Theorem 30.2.** Let $k$ be an integer and let $B : Z^k \to H$ be a mapping from sequences of $k$ examples to the hypothesis class. Let $m \ge 2k$ be a training set size and let $A : Z^m \to H$ be a learning rule that receives a training sequence $S$ of size $m$ and returns a hypothesis such that $A(S) = B(z_{i_1}, \dots, z_{i_k})$ for some $(i_1, \dots, i_k) \in [m]^k$. Let $V = \{z_j : j \notin (i_1, \dots, i_k)\}$ be the set of examples which were not selected for defining $A(S)$. Then, with probability of at least $1 - \delta$ over the choice of $S$ we have
--   $$L_D(A(S)) \le L_V(A(S)) + \sqrt{L_V(A(S))\frac{4k\log(m/\delta)}{m}} + \frac{8k\log(m/\delta)}{m}.$$
--
--   Formally: the loss takes values in $[0,1]$, $k \ge 1$, $m \ge 1$, the selection rule is arbitrary, and $(T, z) \mapsto \ell(B(T), z)$ is measurable.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §30.1 p. 411, Theorem 30.2 with its proof

import Definitions.Def_UnderstandingML_Compression

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 30.2** (p. 411). Let `k` be an integer and let `B : Z^k → H` be a mapping from
sequences of `k` examples to the hypothesis class. Let `m ≥ 2k` be a training set size and let
`A : Z^m → H` be a learning rule with `A(S) = B(z_{i₁}, …, z_{i_k})` for some `(i₁, …, i_k) ∈ [m]^k`.
Let `V` be the set of examples not selected for defining `A(S)`. Then, with probability of at
least `1 − δ` over the choice of `S`,
`L_D(A(S)) ≤ L_V(A(S)) + √(L_V(A(S)) · 4k log(m/δ)/m) + 8k log(m/δ)/m`.
The loss takes values in `[0, 1]`, `k ≥ 1`, `m ≥ 1`, `(T, z) ↦ ℓ(B(T), z)` is measurable; the
selection rule is arbitrary. -/
theorem compression_bound {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (k m : ℕ) (hk : 1 ≤ k) (hm : 2 * k ≤ m) (hm0 : 0 < m) (B : (Fin k → Z) → Hyp)
    (hB : Measurable (fun p : (Fin k → Z) × Z ↦ loss (B p.1) p.2))
    (sel : (Fin m → Z) → Fin k → Fin m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw D m {S | heldOutRisk loss sel S (compressedHyp B sel S) +
        Real.sqrt (heldOutRisk loss sel S (compressedHyp B sel S) * 4 * k * Real.log (m / δ) / m) +
        8 * k * Real.log (m / δ) / m < risk loss D (compressedHyp B sel S)} ≤
      ENNReal.ofReal δ := by sorry

end UnderstandingML
