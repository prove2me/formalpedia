-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_7
-- name    : QTDecode.Parallel.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:01.452607+00:00
-- url     : https://prove2.me/theorems/5e018058-3a89-4d1e-a8e0-550fdd861a92
-- title:
--   Lemma 7, p. 13 — a minimal representation of a coset-minimal x ∈ 𝒞₁ ∖ 𝒞₀^⊥ is also minimal for x⁰
-- statement:
--   Let $\mathcal C_1$ be the Tanner code on $\mathcal G^\square_1$ with local code $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$ and $\mathcal C_0^\perp$ the span of the $\sigma_x$-generators (codewords of $C_A\otimes C_B$ placed on the $Q$-neighbourhoods of $V_0$). For $x\in\mathcal C_1$, a representation $(C_0,R_0,C_1,R_1)$ writes $x=C_1+R_0=C_0+R_1$ with $C_j$ a sum of $C_A$-columns and $R_i$ a sum of $C_B$-rows; its norm is $\|C_0\|+\|R_0\|+\|C_1\|+\|R_1\|$, and $\|x\|$ is the least norm of a representation of $x$. Set $x^0:=C_0+R_0=C_1+R_1$.
--
--   Let $x\in\mathcal C_1\setminus\mathcal C_0^\perp$, let $(C_0,R_0,C_1,R_1)$ be a minimal representation of $x$, and suppose that $\|x\|$ is the minimum norm in the coset $x+\mathcal C_0^\perp$. Then $(C_0,R_0,C_1,R_1)$ is also a minimum representation of $x^0$: for every representation $(C_0',R_0',C_1',R_1')$ of $x^0$, i.e. $x^0=C_0'+R_0'=C_1'+R_1'$,
--   $$\|C_0\|+\|R_0\|+\|C_1\|+\|R_1\|\ \le\ \|C_0'\|+\|R_0'\|+\|C_1'\|+\|R_1'\|.$$
--
--   It allows robustness to be applied at the vertices of $V_0$ as well as $V_1$ in the distance argument (Lemma 10).
--
--   **Formalization Note** "Minimal representation of $x$ with $\|x\|$ the minimum norm in the coset" is encoded as two hypotheses: the norm of the given representation is at most that of every representation of $x$, and of every representation of every $y\in x+\mathcal C_0^\perp$. The page's "minimum representation for $x^0$" means minimal.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 13, Lemma 7 (representations and norm defined on pp. 12–13)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 7, p. 13. Let `x ∈ 𝒞₁ ∖ 𝒞₀^⊥` and let `D = (C₀, R₀, C₁, R₁)` be a minimal representation of
`x` whose norm `‖x‖` is the minimum norm in the coset `x + 𝒞₀^⊥` (`𝒞₀^⊥` is the span of the
`σ_x`-generators, `qtSigmaXSpan`). Then `D` is also a minimum representation of
`x⁰ = C₀ + R₀ = C₁ + R₁`: no representation of `x⁰` has smaller norm. -/
theorem lemma_7 {G : Type} [Group G] [Fintype G] [DecidableEq G] {A B : Finset G}
    (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (x : G × A × B → ZMod 2) (hx1 : x ∈ qtCode1 CA CB) (hx0 : x ∉ qtSigmaXSpan CA CB)
    (D : Decomp (G × A × B)) (hD : IsRepr CA CB x D)
    (hDmin : ∀ D', IsRepr CA CB x D' → decompNorm D ≤ decompNorm D')
    (hcoset : ∀ y, x + y ∈ qtSigmaXSpan CA CB → ∀ D', IsRepr CA CB y D' →
      decompNorm D ≤ decompNorm D') :
    ∀ D', IsRepr0 CA CB (reprZero D) D' → decompNorm D ≤ decompNorm D' := by sorry

end QTDecode.Parallel
