-- Prove2me | Theorems.Thm_UnderstandingML_covering_contraction
-- name    : UnderstandingML.covering_contraction
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:49:22.736038+00:00
-- url     : https://prove2.me/theorems/f9b939e3-7df5-4a89-b2de-528251b64dec
-- title:
--   Lemma 27.3: for coordinatewise ρ-Lipschitz φ, N(ρr, φ ∘ A) ≤ N(r, A)
-- statement:
--   **Lemma 27.3.** For each $i \in [m]$, let $\varphi_i : \mathbb{R} \to \mathbb{R}$ be a $\rho$-Lipschitz function; namely, for all $\alpha, \beta \in \mathbb{R}$ we have $|\varphi_i(\alpha) - \varphi_i(\beta)| \le \rho|\alpha - \beta|$. For $a \in \mathbb{R}^m$ let $\varphi(a)$ denote the vector $(\varphi_1(a_1), \dots, \varphi_m(a_m))$. Let $\varphi \circ A = \{\varphi(a) : a \in A\}$. Then, $N(\rho r, \varphi \circ A) \le N(r, A)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §27.1.1 p. 389, Lemma 27.3 with its proof

import Definitions.Def_UnderstandingML_Covering

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 27.3** (p. 389). For each `i ∈ [m]`, let `φᵢ : ℝ → ℝ` be a `ρ`-Lipschitz function.
For `a ∈ ℝ^m` let `φ(a) = (φ₁(a₁), …, φ_m(a_m))` and `φ ∘ A = {φ(a) : a ∈ A}`. Then
`N(ρ r, φ ∘ A) ≤ N(r, A)`. -/
theorem covering_contraction {m : ℕ} (A : Set (Fin m → ℝ)) (ρ : NNReal) (φ : Fin m → ℝ → ℝ)
    (hφ : ∀ i, LipschitzWith ρ (φ i)) (r : ℝ) :
    coveringNumber (ρ * r) ((fun a i ↦ φ i (a i)) '' A) ≤ coveringNumber r A := by sorry

end UnderstandingML
