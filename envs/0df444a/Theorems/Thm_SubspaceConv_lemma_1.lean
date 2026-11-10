-- Prove2me | Theorems.Thm_SubspaceConv_lemma_1
-- name    : SubspaceConv.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:16.649064+00:00
-- url     : https://prove2.me/theorems/10f9ac8b-0e08-4c55-bb7a-4e431f282199
-- title:
--   Lemma 1 — crossing subspaces $U(B,x+B)=(B\times\{0\})+\langle(x,1)\rangle$
-- statement:
--   Let $H=\mathbb F_q^{n}\times\{0\}\le\mathbb F_q^{n+1}$. Every subspace $U\le\mathbb F_q^{n+1}$ with $U\not\le H$ has a unique pair $(B,x+B)$, $B\le\mathbb F_q^n$, $x+B\in\mathbb F_q^n/B$, such that
--   $$U=U(B,x+B):=(B\times\{0\})+\left\langle\binom{x}{1}\right\rangle .$$
--   For every such crossing subspace, $B\times\{0\}=U\cap H$ and $\dim U=\dim B+1$. For $U_i=U(B_i,x_i+B_i)$, $i=1,2$,
--   $$U_1\le U_2\iff B_1\le B_2\ \text{and}\ x_1-x_2\in B_2 .$$
--
--   This coordinate change on crossing subspaces (a direction $B$ and a translation $x+B$) is what lets the recursion keep the direction as a subspace coordinate and Fourier-transform the translation.
--
--   **Formalization Note** The paper's ambient space $\mathbb F_q^n$ is $\mathbb F_q^{n+1}$ here. Uniqueness is: any other presentation $U=U(B',x')$ has $B'=B$ and $x'-x\in B$.
--
--   Differences from the source:
--   - encoding: ambient F_q^n with H = F_q^{n−1} × {0} → Fin (n+1) → F with H the vectors whose last coordinate is 0, B ≤ Fin n → F; reason: avoids natural-number subtraction; the paper needs n ≥ 1, i.e. the instances n+1 ≥ 1
--   - encoding: a unique pair (B, x + B) → some (B, x) with U = U(B, x), and every (B′, x′) with U = U(B′, x′) has B′ = B and x′ − x ∈ B; reason: a coset x + B is given by a representative modulo B
--   - encoding: "Here B × {0} = U ∩ H and dim U = dim B + 1" for U ∈ X_H → stated for every U(B, x), together with U(B, x) ≰ H; reason: X_H is exactly the set of the U(B, x) by the first clause, so the two forms say the same
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), Lemma 1, eq. (3), p.6 (PDF p.7)

import Mathlib
import Definitions.Def_SubspaceConv_crossSub

namespace SubspaceConv

/-- **Lemma 1** (Crossing subspaces), Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), p.6 (PDF p.7). Let `H = F_q^{n} × {0}` in
`F_q^{n+1}`. Every subspace `U ≰ H` has a unique pair `(B, x + B)` with
`U = U(B, x + B) := (B × {0}) + ⟨(x, 1)⟩`, `B ≤ F_q^n`. Here `B × {0} = U ∩ H` and
`dim U = dim B + 1`. For `U_i = U(B_i, x_i + B_i)`, `U_1 ≤ U_2 ⟺ B_1 ≤ B_2 ∧ x_1 − x_2 ∈ B_2`.

**Formalization Note** The paper's ambient `F_q^n` is `Fin (n+1) → F` here (so its `n − 1` is
`n`), and `H` is "last coordinate `= 0`". Uniqueness of the pair `(B, x + B)` is stated as:
any other presentation `U = U(B', x')` has `B' = B` and `x' − x ∈ B`. The facts
`U ∩ H = B × {0}`, `dim U = dim B + 1` and `U ≰ H` are stated for every `U(B, x)`. -/
theorem lemma_1 (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (∀ U : Submodule F (Fin (n+1) → F), ¬ U ≤ hyperplane F n →
      ∃ B : Submodule F (Fin n → F), ∃ x : Fin n → F, U = crossSub B x ∧
        ∀ (B' : Submodule F (Fin n → F)) (x' : Fin n → F),
          U = crossSub B' x' → B' = B ∧ x' - x ∈ B) ∧
    (∀ (B : Submodule F (Fin n → F)) (x : Fin n → F),
      ¬ crossSub B x ≤ hyperplane F n ∧
      crossSub B x ⊓ hyperplane F n = insideSub B ∧
      Module.finrank F (crossSub B x) = Module.finrank F B + 1) ∧
    (∀ (B₁ B₂ : Submodule F (Fin n → F)) (x₁ x₂ : Fin n → F),
      crossSub B₁ x₁ ≤ crossSub B₂ x₂ ↔ B₁ ≤ B₂ ∧ x₁ - x₂ ∈ B₂) := by sorry

end SubspaceConv
