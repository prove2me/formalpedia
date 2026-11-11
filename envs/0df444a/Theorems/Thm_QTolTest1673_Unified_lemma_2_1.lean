-- Prove2me | Theorems.Thm_QTolTest1673_Unified_lemma_2_1
-- name    : QTolTest1673.Unified.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:58.346659+00:00
-- url     : https://prove2.me/theorems/b49733a4-c8cc-4575-bf86-7ed8873ff621
-- title:
--   Lemma 2.1 — orthonormality of characters, Fourier expansion and Parseval's identity
-- statement:
--   For $u,x\in\mathbb F_2^n$ let $\chi_u(x)=(-1)^{u\cdot x}$, and for a Boolean function $f:\mathbb F_2^n\to\{\pm1\}$ let $\hat f(u)=\mathbb E_x f(x)\chi_u(x)$, with $x$ uniform. The characters form an orthonormal basis of the real functions on $\mathbb F_2^n$:
--
--   1. for all $u,v$,
--   $$\mathbb E_x\,\chi_u(x)\chi_v(x)=\mathbf 1_{u=v};$$
--   2. the $2^n$ characters are linearly independent and span all functions $\mathbb F_2^n\to\mathbb R$;
--   3. every Boolean $f$ satisfies the Fourier expansion $f(x)=\sum_u\hat f(u)\chi_u(x)$ for all $x$;
--   4. every Boolean $f$ satisfies Parseval's identity $\sum_u\hat f(u)^2=1$.
--
--   This is the basic Fourier toolkit of the paper: Parseval makes $u\mapsto\hat f(u)^2$ a probability distribution, the one sampled by a single quantum query, and orthonormality turns mean squares of Fourier sums into sums of squared coefficients.
--
--   Differences from the source:
--   - encoding: $f:\mathbb F_2^n\to\{\pm1\}$ → its bit function `BoolFn n` with $f=(-1)^{b_f}$ (`toSign`); reason: a bijection; the XOR oracle adds $b_f=(1-f)/2$; same instances
--   - encoding: uniform expectation $\mathbb E_x$ → $2^{-n}\sum_x$; reason: definition of the uniform expectation on $\mathbb F_2^n$
--   - encoding: the characters form an orthonormal basis → orthonormality for $\mathbb E_x$ plus `LinearIndependent` and span $=\top$ in the real functions on $\mathbb F_2^n$; reason: the linear-algebra meaning of an orthonormal basis; all three displayed identities are kept
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), source.pdf SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, Lemma 2.1, p. 14

import Definitions.Def_FourierDimTesting102_Quantum_Model

namespace QTolTest1673.Unified

open FourierDimTesting102.Quantum

/-- Lemma 2.1, p. 14 (Fourier expansion and Parseval's identity). The characters
`χ_u(x) = (-1)^{u·x}` are orthonormal for `⟨g, h⟩ = E_x g(x) h(x)` and form a basis of the real
functions on `F₂ⁿ`; every `{±1}`-valued `f` satisfies `f(x) = ∑_u f̂(u) χ_u(x)` and
`∑_u f̂(u)² = 1`. -/
theorem lemma_2_1 (n : ℕ) :
    (∀ u v : V n, ((2 : ℝ) ^ n)⁻¹ * ∑ x : V n, chi u x * chi v x = if u = v then 1 else 0) ∧
      LinearIndependent ℝ (fun u : V n => (chi u : V n → ℝ)) ∧
      Submodule.span ℝ (Set.range fun u : V n => (chi u : V n → ℝ)) = ⊤ ∧
      (∀ (f : BoolFn n) (x : V n), toSign f x = ∑ u : V n, coeff f u * chi u x) ∧
      (∀ f : BoolFn n, ∑ u : V n, coeff f u ^ 2 = 1) := by sorry

end QTolTest1673.Unified
