-- Prove2me | Theorems.Thm_TensorIso233_BQP_lemma_5_3
-- name    : TensorIso233.BQP.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:28.791458+00:00
-- url     : https://prove2.me/theorems/155afad9-c369-4887-839d-a465c45b98e0
-- title:
--   Lemma 5.3 — the pure-cube flag and adapted pairs
-- statement:
--   For $D\in\mathrm{Mat}_3(\mathbb Q)$ let $F_1(D)=\operatorname{im}D\cap\ker D$ and $F_2(D)=\operatorname{im}D+\ker D$ (5.5).
--
--   1. For every nonzero $D$ with $D^3=0$: $\dim F_1=1$, $\dim F_2=2$, and
--   $$
--   D(F_1)=0,\qquad D(F_2)\subseteq F_1,\qquad D(\mathbb Q^3)\subseteq F_2 .
--   $$
--   2. Every tensor $T=(A,B)$ with $f_T=Cx^3$, $C>0$ (5.3), and $B\neq0$ is strictly equivalent to a pair of the form (5.6),
--   $$
--   A=\begin{pmatrix}a&p&r\\0&d&q\\0&0&c\end{pmatrix},\quad B=\begin{pmatrix}0&e&h\\0&0&g\\0&0&0\end{pmatrix},\qquad a,d,c>0,
--   $$
--   whose standard bases are adapted to the flags of $D=A^{-1}B$ and $E=BA^{-1}$ ($F_1=\langle e_1\rangle$, $F_2=\langle e_1,e_2\rangle$ for both).
--   3. If $(A,B)$ and $(A',B')$ are two such adapted pairs and $A'=P(A+tB)Q^{-1}$, $B'=P(\delta B)Q^{-1}$ with $t\in\mathbb Z$, $\delta\in\{\pm1\}$, $P,Q\in GL_3(\mathbb Z)$ (5.4), then $P$ and $Q$ are upper triangular.
--
--   The flag removes the unbounded shear parameter of the pure-cube stabilizer.
--
--   Differences from the source:
--   - generalization: the subspaces (5.5) of D = A⁻¹B for a pair satisfying (5.3) with B ≠ 0 → clause (a) for every nonzero D ∈ Mat₃(ℚ) with D³ = 0; reason: such a D is nonzero with D³ = 0 (p. 19), and (5.5) is defined for every nonzero nilpotent D
--   - reading: the bases respect the flags of D and E; P, Q are upper triangular in adapted bases → adapted pair = shape (5.6) plus the standard bases adapted to the flags of D and E; clause (c) for any two adapted pairs; reason: adaptedness is the flag condition; the shape alone does not force it (D = E₁₂ has F₂ = ⟨e₁, e₃⟩)
-- source:
--   Thomas Huffstutler, Integral 2 × 3 × 3 Tensor Isomorphism is in BQP, STOC 2027 submission #319 (October 2026), Lemma 5.3, p. 21, (5.3)–(5.6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/319.pdf

import Definitions.Def_TensorIso233_BQP_PureCube

namespace TensorIso233.BQP

/-- Lemma 5.3 (p. 21).
(a) For nonzero `D ∈ Mat₃(ℚ)` with `D³ = 0`, the subspaces (5.5) have dimensions one and two
and `D(F₁) = 0`, `D(F₂) ⊆ F₁`, `D(ℚ³) ⊆ F₂`.
(b) Every pair with `f_T = Cx³`, `C > 0` (5.3), and `B ≠ 0` is strictly equivalent to a pair of
the form (5.6) whose standard bases are adapted to the flags of `D = A⁻¹B` and `E = BA⁻¹`.
(c) Every isomorphism (5.4) between two such adapted pairs has `P, Q` upper triangular. -/
theorem lemma_5_3 :
    (∀ D : Matrix (Fin 3) (Fin 3) ℚ, D ≠ 0 → D ^ 3 = 0 →
      Module.finrank ℚ (F1 D) = 1 ∧ Module.finrank ℚ (F2 D) = 2 ∧
      Submodule.map D.mulVecLin (F1 D) = ⊥ ∧ Submodule.map D.mulVecLin (F2 D) ≤ F1 D ∧
      LinearMap.range D.mulVecLin ≤ F2 D) ∧
    (∀ (T : Tensor) (c : ℤ), 0 < c → detForm T = cubeX c → T.2 ≠ 0 →
      ∃ T₀ : Tensor, StrictEquiv T T₀ ∧ IsAdapted T₀) ∧
    (∀ T₀ T₀' : Tensor, IsAdapted T₀ → IsAdapted T₀' →
      ∀ (t δ : ℤ) (P Q : GL3), δ ∈ ({1, -1} : Set ℤ) →
        T₀'.1 = (P : Mat3) * (T₀.1 + t • T₀.2) * ((Q⁻¹ : GL3) : Mat3) →
        T₀'.2 = (P : Mat3) * (δ • T₀.2) * ((Q⁻¹ : GL3) : Mat3) →
        Matrix.BlockTriangular (P : Mat3) id ∧ Matrix.BlockTriangular (Q : Mat3) id) := by sorry

end TensorIso233.BQP
