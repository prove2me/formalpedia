-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_affine_to_conical
-- name    : UnaryParityLifting.Exact.affine_to_conical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:46.978194+00:00
-- url     : https://prove2.me/theorems/d0c03827-aaef-47c7-ab12-7261e819138e
-- title:
--   Lemma 3.8 — Affine-to-conical decomposition
-- statement:
--   Let $g$ be a surjective 1-stifling gadget, with $c_g=-\log_2(1-\delta_g/2)$ fixed by (3.3). For all $N,R\ge1$, and every affine subspace $A\subseteq\mathbb F_2^{mN}$, including the empty set, there are functions $J_A,E_A$ with
--   $$A_g\mathbf1_A=J_A+E_A.$$
--   The function $J_A$ has a nonnegative conical representation of degree at most $R$ and coefficient sum at most $2^R$. For every $z$,
--   $$0\le J_A(z)\le(A_g\mathbf1_A)(z)\le1,\qquad 0\le E_A(z)\le2^{-c_gR},$$
--   and its Walsh–Fourier error satisfies
--   $$\|E_A\|_1\le2^{-c_gR}.$$
--
--   There is no restriction $R\le N$, nor any rank, codimension, or block-support hypothesis on $A$. The same gadget constant works in all dimensions. This is the approximation statement that controls conical mass and Fourier error jointly.
--
--   Differences from the source:
--   - encoding: coordinates indexed by [N] and [m], bits in {0,1} → Fin N and Fin m, Bool bits with false = 0 and true = 1; reason: zero-based labels and the explicit bit maps preserve every assignment
--   - encoding: surjective gadget convention of Definition 2.5, retained throughout Sections 3–4 → an explicit Function.Surjective g hypothesis; reason: excludes empty gadget fibers and the zero-bit vacuity of the reused stifling predicate without excluding any source gadget
--   - encoding: nonnegative finite sums of conjunctions, identical terms collected → one NNReal coefficient for each distinct Option Bool term; reason: the finite term type includes every consistent conjunction, including the empty term, and degree constrains nonzero terms before cancellation
--   - encoding: Walsh norm with chi_U(z) = (-1) to the sum of the bits in U → FourierEntropyApprox.spectralNorm on Bool assignments, with true giving Walsh sign -1; reason: the referenced code has exactly the same uniform normalization, characters and empty Fourier set
--   - encoding: affine subspace A, possibly empty as explicitly covered by the proof → Mathlib AffineSubspace over ZMod 2, pulled back along the bit bijection; reason: the bottom affine subspace is empty, so this includes the source empty case and every other affine set
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; pp.11–13, Lemma 3.8, equations (3.7)–(3.8); p.9, equation (3.3)

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_affineIndicators
import Definitions.Def_UnaryParityLifting_Exact_averaging
import Definitions.Def_UnaryParityLifting_Exact_conicalRepresentations
import Definitions.Def_FourierEntropyApprox_fourierCoeff

namespace UnaryParityLifting.Exact

/-- Alekseev, STOC 2027 submission #567 (October 2026), p.11, Lemma 3.8.
A may be empty. R is not required to be at most N. -/
theorem affine_to_conical (m N R : ℕ) (g : (Fin m → Bool) → Bool)
    (hg : Function.Surjective g) (hstifling : LiftSAParity.IsOneStifling g)
    (hN : 1 ≤ N) (hR : 1 ≤ R)
    (A : AffineSubspace (ZMod 2) ((Fin N × Fin m) → ZMod 2)) :
    ∃ (J : ConicalRepresentation (Fin N)) (E : (Fin N → Bool) → ℝ),
      J.DegreeLE R ∧ J.mass ≤ (2 : ℝ) ^ R ∧
      (∀ z, average g (affineIndicator A) z = J.value z + E z) ∧
      (∀ z, 0 ≤ J.value z ∧ J.value z ≤ average g (affineIndicator A) z ∧
        average g (affineIndicator A) z ≤ 1) ∧
      FourierEntropyApprox.spectralNorm E ≤ errorBound g R ∧
      (∀ z, 0 ≤ E z ∧ E z ≤ errorBound g R) := by sorry

end UnaryParityLifting.Exact
