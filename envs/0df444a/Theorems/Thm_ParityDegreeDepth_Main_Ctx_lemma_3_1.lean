-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_Ctx_lemma_3_1
-- name    : ParityDegreeDepth.Main.Ctx.lemma_3_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:25:05.158006+00:00
-- url     : https://prove2.me/theorems/39bfc1c9-bf21-5f54-bdcf-71f723861be4
-- title:
--   Lemma 3.1 over the public context: the degree recursion
-- statement:
--   Let $p:\mathbb F_2^n\to\mathbb F_2$ have exact degree $d\ge2$. Suppose $\Gamma(j)\ge0$ for $2\le j\le d$. For every degree-$j$ affine restriction $q$ of $p$ with $3\le j\le d$, assume $c(\Delta^j q)\le\Gamma(j)$; for every degree-two restriction assume $D_\oplus((-1)^q)\le1+\Gamma(2)$. Then
--   $$D_\oplus((-1)^p)\le1+\sum_{j=2}^d\Gamma(j).$$
--   Here $c(T)$ is the least codimension of a subspace on which $T$ vanishes in all slots. Restrictions range over every affine coordinate injection in every dimension.
--
--   The statement expresses the total cost of the degree recursion using the same cost schedule on every branch.
--
--   **Formalization Note.** This is the mission milestone Lemma 3.1 with the identical Lean statement, but stated over the public shared context `Def_ParityDegreeDepth_Main_Context` (the definitions used by the paper's Supplement items) instead of private in-file copies, which match that context verbatim. A private `inductive ParityTree` in a statement can never be matched by the verifier, because a separately compiled solution cannot refer to another module's private inductive. Over the public context the statement is checkable.
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 3.1, PDF page 6 / printed page 5.

import Mathlib
import Definitions.Def_ParityDegreeDepth_Main_Context

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main.Ctx

open ParityDegreeDepth.Main

/-- Lemma 3.1 of Zhang, STOC 2027 submission #798, over the public context `Def_ParityDegreeDepth_Main_Context`. -/
theorem lemma_3_1 {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 2 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) (Γ : ℕ → ℝ)
    (hΓ : ∀ j ∈ Finset.Icc 2 d, 0 ≤ Γ j)
    (hhigh : ∀ (m : ℕ) (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
      (a : Vec n (ZMod 2)), Function.Injective B → ∀ j, 3 ≤ j → j ≤ d →
      anfDegree (p ∘ affineMap B a) = (j : WithBot ℕ) →
      (vanishingCodim (topForm (p ∘ affineMap B a) j) : ℝ) ≤ Γ j)
    (hquad : ∀ (m : ℕ) (B : Vec m (ZMod 2) →ₗ[ZMod 2] Vec n (ZMod 2))
      (a : Vec n (ZMod 2)), Function.Injective B →
      anfDegree (p ∘ affineMap B a) = (2 : WithBot ℕ) →
      (parityDepth (phase (p ∘ affineMap B a)) : ℝ) ≤ 1 + Γ 2) :
    (parityDepth (phase p) : ℝ) ≤ 1 + ∑ j ∈ Finset.Icc 2 d, Γ j := by sorry

end ParityDegreeDepth.Main.Ctx
