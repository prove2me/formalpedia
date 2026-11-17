-- Prove2me | Theorems.Thm_PhaseEncodedQGE_Supplement_theorem_6_1
-- name    : PhaseEncodedQGE.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:33:32.082766+00:00
-- url     : https://prove2.me/theorems/26771d7c-f807-45d5-ac54-421056521b94
-- title:
--   Theorem 6.1 — second-purity closures under PE-X1 (in $C_3,C_4,D_\diamond$) and PE-QX1 (in $D_\diamond$ alone)
-- statement:
--   Let $M_2(G;\beta)=\sum_x p_G(x;\beta)^2$ be the output purity and $M_2''(G;0)$ its second derivative in $\beta$ at $0$; write $c=\cos(\eta/2)$, $s=\sin(\eta/2)$, $L=c^4+s^4$.
--
--   1. For every simple cubic graph $G$ of order $n$, under PE-X1,
--   $$M_2''(G;0)=A_n+b_3C_3(G)+b_4C_4(G)+b_DD_\diamond(G),$$
--   with $A_n,b_3,b_4,b_D$ depending on $n,\eta,\gamma$ and not on $G$; here $b_3,b_4,b_D$ are the closure coefficients of Theorem B.17.
--   2. Each of $b_3$, $b_4$, $b_D$ is $L^n=(c^4+s^4)^n$ times a function of $(\eta,\gamma)$.
--   3. At the schedule $(\eta,\gamma)=(23/8,2)$ the three coefficients $b_3,b_4,b_D$ are nonzero for every $n$.
--   4. Under PE-QX1,
--   $$M_2''(G;0)=A^H_n+4\cdot2^{-n}\sin^6(\gamma)\,D_\diamond(G)$$
--   with $A^H_n$ independent of $G$.
--
--   The degree-aware preparation exposes $(C_3,C_4,D_\diamond)$ at second order, while the Hadamard preparation exposes $D_\diamond$ alone: the purity of depth-one MaxCut QAOA on a cubic graph sees, at second order in $\beta$, the $K_4-e$ count and nothing else.
--
--   **Formalization Note** $C_3$, $C_4$ are subgraph cycle counts ($C_4$ includes chorded four-cycles) and $D_\diamond$ counts not necessarily induced copies of $K_4-e$. "Times a function of $(\eta,\gamma)$" is one function $g$ with $b(n,\eta,\gamma)=L^n g(\eta,\gamma)$ for all $n,\eta,\gamma$. The paper's reason for the nonvanishing (the factor $L$ per spectator vertex and interval enclosures at $n=14$) is its proof route.
--
--   Differences from the source:
--   - reading: "under PE-X1" (angles unrestricted in the statement; Theorem B.17: "in the domain of the kernel formulas") → every $\eta,\gamma\in\mathbb R$; reason: Remark B.18: the coefficients are continuous extensions of finite spin sums, defined at every angle
--   - reading: "$A_n,b_3,b_4,b_D$ depending on $n,\eta,\gamma$ and not on $G$" → $b_3,b_4,b_D$ are the explicit coefficients (66)–(67) of Theorem B.17; $\exists A_n$ for each $(n,\eta,\gamma)$ before $\forall G$; reason: the theorem cites Theorem B.17 for these coefficients, and the nonvanishing clause is about them; fresh existential coefficients would let the closure be fitted at small n
--   - encoding: $F_{a,k}$ in $b_3,b_4,b_D$ → $L^{n-N}$ times the kernel (53) of the roots of the local motif of class $(a,k)$; reason: equals the pair kernel of every class-(a,k) pair of every cubic graph on n vertices (Corollary B.4) and is defined at every n for every class
--   - encoding: "each of $b_3,b_4,b_D$ is $L^n$ times a function of $(\eta,\gamma)$" → $\exists g:\mathbb R\to\mathbb R\to\mathbb R,\ \forall n\,\eta\,\gamma,\ b(n,\eta,\gamma)=L^n g(\eta,\gamma)$; reason: direct transcription
--   - reading: "because every pair kernel carries a factor $L$ …, so the interval enclosures at $n=14$ … make the three coefficients nonzero" → only the conclusion: $b_3,b_4,b_D\ne0$ at $(\eta,\gamma)=(23/8,2)$ for every $n$; reason: the because-clause is the proof route, not a further claim
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §6, p.12 (PDF p.13), Theorem 6.1, eq. (16); App. B.2.5–B.2.6, pp.32–33 (PDF pp.33–34), Theorems B.17, B.22

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
import Definitions.Def_PhaseEncodedQGE_Supplement_GraphCounts
import Definitions.Def_PhaseEncodedQGE_Supplement_Purity
set_option autoImplicit false

namespace PhaseEncodedQGE.Supplement

/-- Theorem 6.1, second-purity closures (Miller, Lee, *Structural Accessibility in Phase-Encoded
Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), §6, p.12; Theorems B.17 and
B.22, Corollary B.23).

For every simple cubic graph `G` of order `n`, under PE-X1,
`M″₂(G; 0) = A_n + b₃ C₃(G) + b₄ C₄(G) + b_D D⋄(G)` (16), with `A_n, b₃, b₄, b_D` depending on
`n, η, γ` and not on `G`. Each of `b₃, b₄, b_D` is `Lⁿ = (c⁴ + s⁴)ⁿ` times a function of `(η, γ)`,
and the three coefficients are nonzero at the schedule for every `n`. Under PE-QX1,
`M″₂(G; 0) = A^H_n + 4 · 2⁻ⁿ sin⁶(γ) D⋄(G)` with `A^H_n` independent of `G`.

**Formalization Note** `b₃, b₄, b_D` are the coefficients of Theorem B.17 (`closureB3`, `closureB4`,
`closureBD` at the PE-X1 preparation `(θ, φ) = (η, −π/2)`), the same objects, not fresh
existentials; `A_n` and `A^H_n` are existentially quantified for each `(n, η, γ)` resp. `(n, γ)`
before the graph. "Each is `Lⁿ` times a function of `(η, γ)`" is: there is one `g : ℝ → ℝ → ℝ`
with `b(n, η, γ) = (c⁴ + s⁴)ⁿ g(η, γ)` for all `n, η, γ`. The schedule is `(η, γ) = (23/8, 2)`; the
nonvanishing for every `n` is a conclusion. PE-QX1 is the Hadamard preparation with one `X`
mixer; `2⁻ⁿ` is `(2⁻¹)ⁿ`. `M″₂` is `purityCurv`; `C₃`, `C₄`, `D⋄` are subgraph counts. The
PE-X1 closure is stated for all `η, γ ∈ ℝ` (the kernels are finite spin sums, Remark B.18). The
sentence's reason ("because every pair kernel carries a factor `L` …, so the interval enclosures at
`n = 14` … make the three coefficients nonzero") is the paper's proof route, not a further claim. -/
theorem theorem_6_1 :
    (∀ (n : ℕ) (η γ : ℝ), ∃ A : ℝ, ∀ G : SimpleGraph (Fin n), IsCubic G →
      purityCurv (degPrep G η) .X 1 G γ =
        A + closureB3 η (-(Real.pi / 2)) γ n * (cycleCount G 3 : ℝ) +
          closureB4 η (-(Real.pi / 2)) γ n * (cycleCount G 4 : ℝ) +
          closureBD η (-(Real.pi / 2)) γ n * (diamondCount G : ℝ)) ∧
    (∃ g : ℝ → ℝ → ℝ, ∀ (n : ℕ) (η γ : ℝ), closureB3 η (-(Real.pi / 2)) γ n =
      (Real.cos (η / 2) ^ 4 + Real.sin (η / 2) ^ 4) ^ n * g η γ) ∧
    (∃ g : ℝ → ℝ → ℝ, ∀ (n : ℕ) (η γ : ℝ), closureB4 η (-(Real.pi / 2)) γ n =
      (Real.cos (η / 2) ^ 4 + Real.sin (η / 2) ^ 4) ^ n * g η γ) ∧
    (∃ g : ℝ → ℝ → ℝ, ∀ (n : ℕ) (η γ : ℝ), closureBD η (-(Real.pi / 2)) γ n =
      (Real.cos (η / 2) ^ 4 + Real.sin (η / 2) ^ 4) ^ n * g η γ) ∧
    (∀ n : ℕ, closureB3 (23 / 8) (-(Real.pi / 2)) 2 n ≠ 0 ∧
      closureB4 (23 / 8) (-(Real.pi / 2)) 2 n ≠ 0 ∧
      closureBD (23 / 8) (-(Real.pi / 2)) 2 n ≠ 0) ∧
    (∀ (n : ℕ) (γ : ℝ), ∃ A : ℝ, ∀ G : SimpleGraph (Fin n), IsCubic G →
      purityCurv (hadPrep n) .X 1 G γ =
        A + 4 * (2 : ℝ)⁻¹ ^ n * Real.sin γ ^ 6 * (diamondCount G : ℝ)) := by sorry

end PhaseEncodedQGE.Supplement
