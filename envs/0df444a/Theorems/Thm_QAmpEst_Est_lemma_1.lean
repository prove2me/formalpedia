-- Prove2me | Theorems.Thm_QAmpEst_Est_lemma_1
-- name    : QAmpEst.Est.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:12.661668+00:00
-- url     : https://prove2.me/theorems/fbf0fafb-6105-42af-8252-f1a44ad476c7
-- title:
--   Lemma 1, pp. 5–6 — QΨ₁ = (1 − 2a)Ψ₁ − 2aΨ₀ and QΨ₀ = 2(1 − a)Ψ₁ + (1 − 2a)Ψ₀
-- statement:
--   Let $\mathcal A$ be a unitary on $\mathcal H = \mathbb C^\iota$, $\chi$ a Boolean function on the basis labels, $|\Psi\rangle = \mathcal A|0\rangle = |\Psi_1\rangle + |\Psi_0\rangle$ the decomposition into good and bad parts, $a = \langle\Psi_1|\Psi_1\rangle$, and $\mathbf Q = -\mathcal A\mathbf S_0\mathcal A^{-1}\mathbf S_\chi$. Then
--   $$\mathbf Q|\Psi_1\rangle = (1-2a)|\Psi_1\rangle - 2a|\Psi_0\rangle, \qquad \mathbf Q|\Psi_0\rangle = 2(1-a)|\Psi_1\rangle + (1-2a)|\Psi_0\rangle .$$
--
--   In particular the subspace spanned by $|\Psi_1\rangle$ and $|\Psi_0\rangle$ is invariant under $\mathbf Q$, which is what reduces amplitude amplification to a rotation in a plane.
--
--   **Formalization Note** $\mathcal A^{-1}$ is the conjugate transpose, and the unitarity hypothesis is what makes the two agree.
-- source:
--   arXiv:quant-ph/0005055v1, Lemma 1, pp. 5–6

import Mathlib
import Definitions.Def_QAmpEst_Est_Setting

open scoped Real Kronecker

namespace QAmpEst.Est

/-- Lemma 1, arXiv:quant-ph/0005055v1, pp. 5–6: with `Ψ₁`, `Ψ₀` the good and bad parts of
`|Ψ⟩ = A|0⟩` and `a = ⟨Ψ₁|Ψ₁⟩`,
`Q|Ψ₁⟩ = (1 − 2a)|Ψ₁⟩ − 2a|Ψ₀⟩` and `Q|Ψ₀⟩ = 2(1 − a)|Ψ₁⟩ + (1 − 2a)|Ψ₀⟩`. -/
theorem lemma_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) :
    let Ψ₁ := goodPart χ (initState A z0)
    let Ψ₀ := badPart χ (initState A z0)
    let a : ℂ := (succProb A χ z0 : ℂ)
    (Qop A χ z0).mulVec Ψ₁ = (1 - 2 * a) • Ψ₁ - (2 * a) • Ψ₀ ∧
      (Qop A χ z0).mulVec Ψ₀ = (2 * (1 - a)) • Ψ₁ + (1 - 2 * a) • Ψ₀ := by sorry

end QAmpEst.Est
