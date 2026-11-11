-- Prove2me | Theorems.Thm_QTolTest1673_Unified_lemma_2_3_mass
-- name    : QTolTest1673.Unified.lemma_2_3_mass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:43.645797+00:00
-- url     : https://prove2.me/theorems/138ef269-30b3-4a80-bb03-b4c8e534bba9
-- title:
--   Lemma 2.3 — the mean square of the block average is the Fourier mass, $\mathbb E_x m_V(x)^2=W_V$ (second identity)
-- statement:
--   Let $f:\mathbb F_2^n\to\{\pm1\}$ and $V\le\mathbb F_2^n$. Define the block average and the Fourier mass
--   $$m_V(x)=\mathbb E_{z\in V^\perp}f(x+z),\qquad W_V=\sum_{u\in V}\hat f(u)^2 .$$
--   Then
--   $$\mathbb E_x\,m_V(x)^2=W_V .$$
--
--   Together with the first identity of Lemma 2.3, $m_V=\sum_{u\in V}\hat f(u)\chi_u$, this relates the block structure of $f$ to the probability $W_V$ that a Fourier sample lands in $V$, which is what the tester estimates.
--
--   Differences from the source:
--   - encoding: $f:\mathbb F_2^n\to\{\pm1\}$ → its bit function `BoolFn n` with $f=(-1)^{b_f}$ (`toSign`); reason: a bijection; the XOR oracle adds $b_f=(1-f)/2$; same instances
--   - encoding: uniform expectation $\mathbb E_x$ → $2^{-n}\sum_x$; reason: definition of the uniform expectation on $\mathbb F_2^n$
--   - encoding: Lemma 2.3 as one statement with two identities → this item states the second identity; the first, $m_V=\sum_{u\in V}\hat f(u)\chi_u$, is the existing platform item `FourierDimTesting102.Quantum.projection_coset_average`, included in this mission as a reference; reason: the conjunction is split between an existing Open item and this item; no clause is dropped
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), source.pdf SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, Lemma 2.3 (second identity), p. 15

import Definitions.Def_FourierDimTesting102_Quantum_Model

namespace QTolTest1673.Unified

open FourierDimTesting102.Quantum

/-- Lemma 2.3, second identity, p. 15: for every subspace `V ≤ F₂ⁿ` and every Boolean `f`, the
mean square of the block average `m_V(x) = E_{z ∈ V^⊥} f(x + z)` is the Fourier mass
`W_V = ∑_{u ∈ V} f̂(u)²`. -/
theorem lemma_2_3_mass {n : ℕ} (W : Submodule (ZMod 2) (V n)) (f : BoolFn n) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ x : V n, cosetAverage W f x ^ 2 = wtIn f W := by sorry

end QTolTest1673.Unified
