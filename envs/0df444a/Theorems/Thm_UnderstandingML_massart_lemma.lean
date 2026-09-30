-- Prove2me | Theorems.Thm_UnderstandingML_massart_lemma
-- name    : UnderstandingML.massart_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:42:44.846856+00:00
-- url     : https://prove2.me/theorems/fecb7068-cdeb-438b-9b4b-bd1c67ca39f0
-- title:
--   Lemma 26.8 (Massart): for a finite A = {a₁,…,a_N} ⊂ ℝ^m with mean ā, R(A) ≤ max_{a∈A} ‖a − ā‖ √(2 log N)/m
-- statement:
--   **Lemma 26.8 (Massart lemma).** Let $A = \{a_1, \dots, a_N\}$ be a finite set of vectors in $\mathbb{R}^m$. Define $\bar a = \frac1N\sum_{i=1}^N a_i$. Then
--   $$R(A) \le \max_{a \in A}\|a - \bar a\|\,\frac{\sqrt{2\log(N)}}{m}.$$
--
--   Formally: $A$ a nonempty finset, Euclidean norms written out.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §26.1.1 pp. 380-381, Lemma 26.8 with its proof

import Definitions.Def_UnderstandingML_Rademacher

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 26.8 (Massart lemma)** (p. 380). Let `A = {a₁, …, a_N}` be a finite set of vectors
in `ℝ^m`. Define `ā = (1/N) ∑ᵢ aᵢ`. Then `R(A) ≤ max_{a ∈ A} ‖a − ā‖ √(2 log(N)) / m`, with the
Euclidean norm. `A` is nonempty. -/
theorem massart_lemma {m : ℕ} (A : Finset (Fin m → ℝ)) (hA : A.Nonempty) :
    rademacher (↑A : Set (Fin m → ℝ)) ≤
      (⨆ a : A, Real.sqrt (∑ i, ((a : Fin m → ℝ) i - (∑ b ∈ A, b i) / A.card) ^ 2)) *
        Real.sqrt (2 * Real.log A.card) / m := by sorry

end UnderstandingML
