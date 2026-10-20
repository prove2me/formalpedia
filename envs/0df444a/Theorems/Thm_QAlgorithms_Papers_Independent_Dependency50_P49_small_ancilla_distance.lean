-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P49_small_ancilla_distance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P49.small_ancilla_distance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:23:08.920149+00:00
-- url     : https://prove2.me/theorems/9017e772-864c-41bd-add1-a873a79e813b
-- title:
--   Small-environment channels approach cb-distance two from maximally mixed replacement
-- statement:
--   For each positive integer $n$, let $R_n:\mathcal B(\mathbb C^n)\to\mathcal B(\mathbb C^n)$ be a completely positive unital complex-linear map. Suppose it admits a Stinespring isometry $V_n:\mathbb C^n\to\mathbb C^n\otimes\mathbb C^{e_n}$, with $e_n>0$ and $e_n/n^2\to0$. Let $S_n(X)=\operatorname{tr}(X)I/n$. Then
--
--   $$\lim_{n\to\infty}\|R_n-S_n\|_{\rm cb}=2.$$
--
--   The cb-norm is unhalved and $S_n$ is the particular maximally mixed replacement channel. The environment need not be minimal. This is the source's extension of the separation argument to every channel with subquadratic environment dimension.
-- source:
--   The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation, arXiv:quant-ph/0605009v1, PDF p. 14, §V, paragraph following Eq. (55)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker Topology ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Information100.P50 (coefficientMap)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

namespace QAlgorithms.Papers.Independent.Dependency50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- The accepted all-Schatten norms at p=top are exactly the source's operator norms.

local notation "inducedNorm" => QAlgorithms.Papers.Independent.Information100.P50.inducedNorm (⊤ : ℝ≥0∞)

local notation "cbNorm" => QAlgorithms.Papers.Independent.Information100.P50.cbNorm (⊤ : ℝ≥0∞)

/-- PDF p.14, paragraph following (55): every channel sequence admitting an
ancilla of dimension o(n^2) tends to cb-distance 2 from the particular maximally
mixed replacement. The index k represents physical dimension k+1. -/
theorem small_ancilla_distance
    (e : ℕ → ℕ) (he : ∀ k, 0 < e k)
    (T : (k : ℕ) → MatrixMap (Fin (k + 1)) (Fin (k + 1)))
    (hT : ∀ k, IsQuantumChannel (T k))
    (V : (k : ℕ) → Matrix (Fin (k + 1) × Fin (e k)) (Fin (k + 1)) ℂ)
    (hV : ∀ k, QAlgorithms.Papers.Independent.Information100.P71.IsStinespring (traceDual (T k)) (V k))
    (hsmall : Tendsto (fun k : ℕ => (e k : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2))
      atTop (𝓝 0)) :
    Tendsto (fun k => cbNorm (T k - uniformDepolarizing (k + 1))) atTop (𝓝 2) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P49

end
