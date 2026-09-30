-- Prove2me | Theorems.Thm_UnderstandingML_contraction_lemma
-- name    : UnderstandingML.contraction_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:43:03.060054+00:00
-- url     : https://prove2.me/theorems/32877bba-825c-4f78-ae08-8969ef934bdc
-- title:
--   Lemma 26.9 (contraction, Kakade–Tewari): for coordinatewise ρ-Lipschitz φ, R(φ ∘ A) ≤ ρ R(A)
-- statement:
--   **Lemma 26.9 (Contraction lemma).** For each $i \in [m]$, let $\varphi_i : \mathbb{R} \to \mathbb{R}$ be a $\rho$-Lipschitz function, namely for all $\alpha, \beta \in \mathbb{R}$ we have $|\varphi_i(\alpha) - \varphi_i(\beta)| \le \rho|\alpha - \beta|$. For $a \in \mathbb{R}^m$ let $\varphi(a)$ denote the vector $(\varphi_1(a_1), \dots, \varphi_m(a_m))$. Let $\varphi \circ A = \{\varphi(a) : a \in A\}$. Then $R(\varphi \circ A) \le \rho\,R(A)$. $A$ is nonempty and bounded.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §26.1.1 pp. 381-382, Lemma 26.9 with its proof

import Definitions.Def_UnderstandingML_Rademacher

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 26.9 (Contraction lemma)** (p. 381). For each `i ∈ [m]`, let `φᵢ : ℝ → ℝ` be a
`ρ`-Lipschitz function. For `a ∈ ℝ^m` let `φ(a) = (φ₁(a₁), …, φ_m(a_m))` and
`φ ∘ A = {φ(a) : a ∈ A}`. Then `R(φ ∘ A) ≤ ρ R(A)`. `A` is nonempty and bounded. -/
theorem contraction_lemma {m : ℕ} (A : Set (Fin m → ℝ)) (hA : A.Nonempty)
    (hb : Bornology.IsBounded A) (ρ : NNReal) (φ : Fin m → ℝ → ℝ)
    (hφ : ∀ i, LipschitzWith ρ (φ i)) :
    rademacher ((fun a i ↦ φ i (a i)) '' A) ≤ ρ * rademacher A := by sorry

end UnderstandingML
