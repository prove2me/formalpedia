-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_lemma_2_11
-- name    : RandTensorIso.Smoothed.lemma_2_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:36:57.38754+00:00
-- url     : https://prove2.me/theorems/5b4c3b71-80e2-40a3-abbd-f9f1b41c0648
-- title:
--   Lemma 2.11 — orbit-close tensors with diagonal gapped Gram matrices are close under diagonal phases
-- statement:
--   Let $A,B\in\mathbb C^{n\times n\times n}$ be such that for every $d\in[3]$ the Gram matrices $G_d(A)$ and $G_d(B)$ are diagonal with (real) diagonal entries in nonincreasing order, and the diagonal entries of each $G_d(A)$ have consecutive gaps at least $\delta$. Suppose $L,R,T\in U(n)$ satisfy $\|(L,R,T)\curvearrowright A-B\|_F<\varepsilon$ for some $0<\varepsilon<\delta/(8(\|A\|_F+\|B\|_F))$. Then there are diagonal phase matrices $D_d=\operatorname{diag}(\omega_d)$, $|\omega_d(i)|=1$, with
--   $$\|(D_1,D_2,D_3)\curvearrowright A-B\|_F<\gamma\varepsilon,\qquad \gamma=1+\frac{5\sqrt n\,\|A\|_F(\|A\|_F+\|B\|_F)}{\delta}.$$
--   This is the deterministic step that reduces the analysis of Algorithm 3 to phase alignment on the cores.
--
--   Differences from the source:
--   - encoding: G_d(A), G_d(B) are diagonal matrices with real entries sorted in nonincreasing order → `IsDiag` and nonincreasing real parts of the diagonal; reason: the diagonal of a Gram matrix is real, so 'real entries' adds nothing
--   - encoding: there exist L, R, T unitary such that … → L, R, T : U n given as arguments with the hypothesis; reason: equivalent; ∃ in a hypothesis
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 26 (PDF 28), Lemma 2.11

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor
import Definitions.Def_RandTensorIso_Smoothed_Spectral

open Matrix

namespace RandTensorIso.Smoothed

/-- Lemma 2.11 (p. 26). Gram matrices of `A` and `B` diagonal with real entries in nonincreasing
order, the diagonal entries of each `G_d(A)` with gaps at least `δ`, and a unitary triple with
`‖(L, R, T) ↷ A − B‖_F < ε` for some `0 < ε < δ/(8(‖A‖_F + ‖B‖_F))`: then diagonal phase matrices
`D₁, D₂, D₃` give `‖(D₁, D₂, D₃) ↷ A − B‖_F < γε`, `γ = 1 + 5√n ‖A‖_F(‖A‖_F + ‖B‖_F)/δ`. -/
theorem lemma_2_11 (n : ℕ) (A B : Tensor3 n) (δ ε : ℝ)
    (hdiagA : ∀ d : Fin 3, (gram d A).IsDiag)
    (hdiagB : ∀ d : Fin 3, (gram d B).IsDiag)
    (hsortA : ∀ d : Fin 3, ∀ i j : Fin n, i ≤ j → (gram d A j j).re ≤ (gram d A i i).re)
    (hsortB : ∀ d : Fin 3, ∀ i j : Fin n, i ≤ j → (gram d B j j).re ≤ (gram d B i i).re)
    (hgapA : ∀ d : Fin 3, ∀ i j : Fin n, j.val = i.val + 1 →
      δ ≤ (gram d A i i).re - (gram d A j j).re)
    (L R T : U n)
    (hclose : frob (act (L : Matrix (Fin n) (Fin n) ℂ) (R : Matrix (Fin n) (Fin n) ℂ)
      (T : Matrix (Fin n) (Fin n) ℂ) A - B) < ε)
    (hε : 0 < ε) (hεδ : ε < δ / (8 * (frob A + frob B))) :
    ∃ ω : Fin 3 → Fin n → ℂ, (∀ d i, ‖ω d i‖ = 1) ∧
      frob (act (diagonal (ω 0)) (diagonal (ω 1)) (diagonal (ω 2)) A - B) <
        (1 + 5 * Real.sqrt n * frob A * (frob A + frob B) / δ) * ε := by sorry

end RandTensorIso.Smoothed
