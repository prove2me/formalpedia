-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_le_sqrt_two_r_frob_of_mem_Mbar
-- name    : WainwrightHDS.NucNorm.nucNorm_le_sqrt_two_r_frob_of_mem_Mbar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:33:27.130015+00:00
-- url     : https://prove2.me/theorems/d44ebe86-f01d-4d29-b84a-9a7ce8e353fe
-- title:
--   Proof of Proposition 10.6 — subspace Lipschitz constant $\Psi(\overline{\mathbb M}(\mathbb U^r,\mathbb V^r))\le\sqrt{2r}$
-- statement:
--   Let $r\ge0$ and let $\mathbb U\subseteq\mathbb R^{d_1}$, $\mathbb V\subseteq\mathbb R^{d_2}$ be linear subspaces of dimension at most $r$. Then every $\Theta\in\overline{\mathbb M}(\mathbb U,\mathbb V)$ satisfies
--
--   $$
--   |||\Theta|||_{\mathrm{nuc}} \;\le\; \sqrt{2r}\;|||\Theta|||_F ,
--   $$
--
--   that is, the subspace Lipschitz constant $\Psi(\overline{\mathbb M}(\mathbb U,\mathbb V)):=\sup_{\Theta\in\overline{\mathbb M}\setminus\{0\}}|||\Theta|||_{\mathrm{nuc}}/|||\Theta|||_F$ is at most $\sqrt{2r}$. This is the quantity that converts the nuclear-norm control of the error into the Frobenius error bound of Proposition 10.6.
--
--   Differences from the source:
--   - generalization: U^r, V^r r-dimensional (spanned by the top r singular vectors of Θ*) → arbitrary subspaces U, V with dim U ≤ r and dim V ≤ r; reason: the bound holds for every such pair, so it specializes to the source's subspaces
--   - encoding: Ψ(M̄) := sup_{Θ ∈ M̄∖{0}} |||Θ|||_nuc/|||Θ|||_F ≤ √(2r) → ∀ Θ ∈ M̄, nucNorm Θ ≤ √(2r)·√(frobSq Θ); reason: equivalent (Θ = 0 satisfies the inequality), and it avoids the junk value of a real supremum
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.2.2, proof of Proposition 10.6, p. 320 (PDF p. 340); Ψ from Definition 9.18, p. 279 (PDF p. 299)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Definitions.Def_WainwrightHDS_NucNorm_Mbar

namespace WainwrightHDS.NucNorm

/-- **Subspace Lipschitz constant `Ψ(𝕄̄(𝕌ʳ, 𝕍ʳ)) ≤ √(2r)`.** If `dim 𝕌 ≤ r` and `dim 𝕍 ≤ r`, then
every `Θ ∈ 𝕄̄(𝕌, 𝕍)` satisfies `|||Θ|||_nuc ≤ √(2r) |||Θ|||_F`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.2.2, proof of Proposition 10.6, p. 320 (PDF p. 340); `Ψ` is Definition 9.18,
p. 279 (PDF p. 299).

Formalization Note: the bound `sup_{Θ ∈ 𝕄̄ \ {0}} |||Θ|||_nuc / |||Θ|||_F ≤ √(2r)` is stated pointwise
(equivalent; `Θ = 0` satisfies it trivially). `|||Θ|||_F = √(frobSq Θ)`. The book's subspaces are
`r`-dimensional; `dim ≤ r` is a generalization. -/
theorem nucNorm_le_sqrt_two_r_frob_of_mem_Mbar {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (r : ℕ) (hU : Module.finrank ℝ U ≤ r) (hV : Module.finrank ℝ V ≤ r)
    (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) (hΘ : Θ ∈ Mbar U V) :
    nucNorm Θ ≤ Real.sqrt (2 * (r : ℝ)) * Real.sqrt (frobSq Θ) := by sorry

end WainwrightHDS.NucNorm
