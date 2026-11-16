-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_Supplement_lemma_C_2
-- name    : ParityDegreeDepth.Main.Supplement.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:49:06.183813+00:00
-- url     : https://prove2.me/theorems/6209e16d-ab9c-48bd-a5d7-8a228abaca5d
-- title:
--   Lemma C.2 — properties of the threshold weight
-- statement:
--   Let $V_n=\mathbb F_2^n$. For a sign function $f:V_n\to\{-1,1\}$, a margin-one sign witness is a real $g$ with $f(x)g(x)\ge1$ for all $x$, and $W(f)$ is the least spectral norm $\|\widehat g\|_1$ of a witness. An affine subspace $H$ is written as $H=\{a+By: y\in\mathbb F_2^m\}$ with $B:\mathbb F_2^m\to\mathbb F_2^n$ injective and linear, and $f|_H(y)=f(a+By)$. For $h\in V_n$, $D_hf(x)=f(x)f(x+h)$. For a polynomial $p:V_n\to\mathbb F_2$ of degree at most $2$, the polar form $\beta_p(u,v)=p(u+v)+p(u)+p(v)+p(0)$ is bilinear and its rank, the polar rank, is even.
--
--   1. **(Restriction.)** Let $f$ be a sign function, $g$ any real function, $B$ injective linear and $a\in V_n$. If $g$ witnesses $f$ then $g|_H$ witnesses $f|_H$, and $\|\widehat{g|_H}\|_1\le\|\widehat g\|_1$. Moreover $W(f|_H)\le W(f)$.
--   2. **(Products and derivatives.)** If $f_1,f_2$ are sign functions and $g_i$ witnesses $f_i$ for $i=1,2$, then $g_1g_2$ witnesses $f_1f_2$ and $\|\widehat{g_1g_2}\|_1\le\|\widehat{g_1}\|_1\|\widehat{g_2}\|_1$. For every sign function $f$, every $k\ge0$ and every $h_1,\dots,h_k\in V_n$,
--   $$
--   W(D_{h_1}\cdots D_{h_k}f)\le W(f)^{2^k}.
--   $$
--   3. **(Quadratic phases.)** If $\deg p\le 2$, $p$ has polar rank $2r$ and $f=(-1)^p$, then every margin-one sign witness $g$ for $f$ satisfies $\|\widehat g\|_1\ge 2^r$, and $W(f)=2^r$.
--   4. **(Nontriviality.)** If $\deg p=d\ge2$ and $f=(-1)^p$, then $W(f)>1$.
--
--   These four properties are exactly what the threshold-weight extension (Theorem 1.5) needs: restriction monotonicity lets every branch of the recursion use the original $W(f)$, the derivative bound and the quadratic identity convert $W$ into a bound on the binary contraction rank, and nontriviality makes the per-degree costs nonnegative.
--
--   **Formalization Note** Sign functions are real functions with values in $\{-1,1\}$; degrees are degrees of the algebraic normal form; the polar rank is the rank of the matrix $\bigl(\beta_p(e_i,e_j)\bigr)_{i,j}$, encoded exactly as in the mission's Lemma 2.6.
--
--   Differences from the source:
--   - encoding: sign functions f, f₁, f₂ : 𝔽₂ⁿ → {−1,1} → real-valued functions with f x = −1 ∨ f x = 1 at every x; reason: the same functions
--   - encoding: W(f) defined as a minimum → the real infimum of the same set of spectral norms; reason: the minimum is attained (paper's remark after Definition C.1), so the values agree; for ±1-valued f the set is nonempty and bounded below
--   - encoding: every affine subspace H and f|H, g|H → every injective 𝔽₂-linear B : 𝔽₂ᵐ → 𝔽₂ⁿ (every m, m = 0 included) and shift a, with f ∘ (a + B·) and g ∘ (a + B·); reason: every affine subspace has such a parametrization, and the restricted functions are taken in its coordinates, as in the mission's Lemma 2.2
--   - encoding: D_{h₁}⋯D_{h_k} f → signDerivatives f h for h : Fin k → 𝔽₂ⁿ, every k ≥ 0, arbitrary (possibly zero or repeated) h_i; reason: the published iterated multiplicative derivative, same function
--   - encoding: degree at most 2 / exactly d, polar rank 2r → anfDegree p ≤ 2 / anfDegree p = d in WithBot ℕ, and rank of the polar-form matrix (contraction of topForm p 2 at the empty anchor tuple) = 2r; reason: the published Context's degree and the mission's Lemma 2.6 encoding of polar rank
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, SHA-256 02e6bad861054e233c6877aa352d0014cf84172cde536433dd6e24588277680b, Lemma C.2 (a)–(d), PDF p. 25 (printed p. 24); Definition C.1 same page; Eq. (5) PDF p. 5 (printed p. 4); polar rank PDF p. 6 (printed p. 5).

import Mathlib
import Definitions.Def_ParityDegreeDepth_Main_Context
import Definitions.Def_ParityDegreeDepth_Main_Supplement_ThresholdWeight

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main.Supplement

open ParityDegreeDepth.Main

/-- Zhang, STOC 2027 submission #798, Lemma C.2 (a)–(d), PDF p. 25 (printed p. 24).
SHA-256 02e6bad861054e233c6877aa352d0014cf84172cde536433dd6e24588277680b.
(a) affine restriction along every injective linear `B` and shift `a`;
(b) products of witnesses, and the derivative bound `W(D_{h₁}⋯D_{h_k} f) ≤ W(f)^(2^k)`;
(c) quadratic phases of polar rank `2r`: every witness has norm `≥ 2^r`, and `W = 2^r`;
(d) `W > 1` for phases of exact degree `d ≥ 2`. -/
theorem lemma_C_2 :
    -- (a)
    (∀ (n m : ℕ) (f g : Vec n (ZMod 2) → ℝ)
        (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2)) (a : Vec n (ZMod 2)),
        (∀ x, f x = -1 ∨ f x = 1) → Function.Injective B →
        (IsSignWitness f g →
          IsSignWitness (f ∘ affineMap B a) (g ∘ affineMap B a) ∧
          spectralNorm (g ∘ affineMap B a) ≤ spectralNorm g) ∧
        thresholdWeight (f ∘ affineMap B a) ≤ thresholdWeight f) ∧
    -- (b)
    (∀ (n : ℕ) (f₁ f₂ g₁ g₂ : Vec n (ZMod 2) → ℝ),
        (∀ x, f₁ x = -1 ∨ f₁ x = 1) → (∀ x, f₂ x = -1 ∨ f₂ x = 1) →
        IsSignWitness f₁ g₁ → IsSignWitness f₂ g₂ →
        IsSignWitness (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) ∧
        spectralNorm (fun x => g₁ x * g₂ x) ≤ spectralNorm g₁ * spectralNorm g₂) ∧
    (∀ (n k : ℕ) (f : Vec n (ZMod 2) → ℝ) (h : Fin k → Vec n (ZMod 2)),
        (∀ x, f x = -1 ∨ f x = 1) →
        thresholdWeight (signDerivatives f h) ≤ thresholdWeight f ^ (2 ^ k)) ∧
    -- (c)
    (∀ (n r : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
        anfDegree p ≤ (2 : WithBot ℕ) →
        (contraction (topForm p 2) (fun i => Fin.elim0 i)).rank = 2 * r →
        (∀ g, IsSignWitness (phase p) g → (2 : ℝ) ^ r ≤ spectralNorm g) ∧
        thresholdWeight (phase p) = (2 : ℝ) ^ r) ∧
    -- (d)
    (∀ (n d : ℕ) (p : Vec n (ZMod 2) → ZMod 2),
        2 ≤ d → anfDegree p = (d : WithBot ℕ) →
        1 < thresholdWeight (phase p)) := by sorry

end ParityDegreeDepth.Main.Supplement
