-- Prove2me | Theorems.Thm_QTolTest1673_Unified_lemma_2_4
-- name    : QTolTest1673.Unified.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:52.030918+00:00
-- url     : https://prove2.me/theorems/11b91d3d-4f92-4f6a-91ba-cc4f18fccfc3
-- title:
--   Lemma 2.4 — correlation with $C_V$, distance to $C_V$ and the mass sandwich $\operatorname{corr}^2\le W_V\le\operatorname{corr}$
-- statement:
--   Let $f:\mathbb F_2^n\to\{\pm1\}$ and $V\le\mathbb F_2^n$, with block average $m_V(x)=\mathbb E_{z\in V^\perp}f(x+z)$, Fourier mass $W_V=\sum_{u\in V}\hat f(u)^2$, and $C_V$ the Boolean functions constant on every coset of $V^\perp$. Then
--
--   1. $\operatorname{corr}(f,C_V)=\mathbb E_x|m_V(x)|$;
--   2. $\displaystyle\operatorname{dist}(f,C_V)=\frac{1-\mathbb E_x|m_V(x)|}{2}$;
--   3. $\operatorname{corr}(f,C_V)^2\le W_V\le\operatorname{corr}(f,C_V)$.
--
--   Here $\operatorname{corr}(f,\mathcal C)=\max_{g\in\mathcal C}\mathbb E_x f(x)g(x)$ and $\operatorname{dist}(f,\mathcal C)=\min_{g\in\mathcal C}\Pr_x[f(x)\ne g(x)]$. The sandwich converts closeness to a block-constant class into Fourier mass, with a square lost on one side; this is the origin of the mass gap $\Gamma$.
--
--   Differences from the source:
--   - encoding: $f:\mathbb F_2^n\to\{\pm1\}$ → its bit function `BoolFn n` with $f=(-1)^{b_f}$ (`toSign`); reason: a bijection; the XOR oracle adds $b_f=(1-f)/2$; same instances
--   - encoding: uniform expectation $\mathbb E_x$ → $2^{-n}\sum_x$; reason: definition of the uniform expectation on $\mathbb F_2^n$
--   - encoding: $\max_{g\in C_V}$, $\min_{g\in C_V}$ → `sSup`/`sInf` of the finitely many values over $C_V$; reason: $C_V$ is finite and contains the constants, so these are attained
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), source.pdf SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, Lemma 2.4, p. 16

import Definitions.Def_QTolTest1673_Unified_Classes

namespace QTolTest1673.Unified

open FourierDimTesting102.Quantum

/-- Lemma 2.4, p. 16 (correlation and Fourier mass). For every subspace `V ≤ F₂ⁿ` and Boolean
`f`, with `m_V` the block average and `C_V` the block-constant class:
`corr(f, C_V) = E_x |m_V(x)|`, `dist(f, C_V) = (1 − E_x |m_V(x)|)/2`, and
`corr(f, C_V)² ≤ W_V ≤ corr(f, C_V)`. -/
theorem lemma_2_4 {n : ℕ} (W : Submodule (ZMod 2) (V n)) (f : BoolFn n) :
    corrToSet f (blockConst W) = ((2 : ℝ) ^ n)⁻¹ * ∑ x : V n, |cosetAverage W f x| ∧
      distToSet f (blockConst W) =
        (1 - ((2 : ℝ) ^ n)⁻¹ * ∑ x : V n, |cosetAverage W f x|) / 2 ∧
      corrToSet f (blockConst W) ^ 2 ≤ wtIn f W ∧
      wtIn f W ≤ corrToSet f (blockConst W) := by sorry

end QTolTest1673.Unified
