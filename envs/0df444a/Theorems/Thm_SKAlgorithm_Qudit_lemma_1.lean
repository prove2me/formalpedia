-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_lemma_1
-- name    : SKAlgorithm.Qudit.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:52.879722+00:00
-- url     : https://prove2.me/theorems/57187885-367f-4a4d-b088-516f65e7082c
-- title:
--   Lemma 1, p. 9 — approximating a group commutator
-- statement:
--   Let $V, W, \tilde V, \tilde W$ be $d \times d$ unitary matrices and $\Delta, \delta$ real numbers such that
--   $$d(V, \tilde V) < \Delta, \quad d(W, \tilde W) < \Delta, \quad d(I, V) < \delta, \quad d(I, W) < \delta .$$
--   Then
--   $$d\big(VWV^\dagger W^\dagger,\ \tilde V \tilde W \tilde V^\dagger \tilde W^\dagger\big) < 8\Delta\delta + 4\Delta\delta^2 + 8\Delta^2 + 4\Delta^3 + \Delta^4 .$$
--
--   In the Solovay-Kitaev recursion $\Delta$ is the current accuracy $\epsilon_{n-1}$ and $\delta$ is of order $\sqrt{\epsilon_{n-1}}$, so the right-hand side is $O(\epsilon_{n-1}^{3/2})$: approximating $V$ and $W$ to accuracy $\epsilon_{n-1}$ approximates their group commutator to the better accuracy $O(\epsilon_{n-1}^{3/2})$.
--
--   **Formalization Note.** $V, W, \tilde V, \tilde W$ are matrices with membership in the unitary group (not necessarily of determinant one), as in the lemma. $d(I, V)$ is $\|I - V\|$ and all distances use the operator norm `QAlgorithms.specNorm`; $V^\dagger$ is the conjugate transpose.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 9, §4.2, Lemma 1, Eq. (14)

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem lemma_1 {d : ℕ} (V W Vt Wt : Matrix (Fin d) (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hVt : Vt ∈ Matrix.unitaryGroup (Fin d) ℂ) (hWt : Wt ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (Δ δ : ℝ) (hVVt : specNorm (V - Vt) < Δ) (hWWt : specNorm (W - Wt) < Δ)
    (hIV : specNorm (1 - V) < δ) (hIW : specNorm (1 - W) < δ) :
    specNorm (V * W * Vᴴ * Wᴴ - Vt * Wt * Vtᴴ * Wtᴴ) <
      8 * Δ * δ + 4 * Δ * δ ^ 2 + 8 * Δ ^ 2 + 4 * Δ ^ 3 + Δ ^ 4 := by sorry

end SKAlgorithm.Qudit
