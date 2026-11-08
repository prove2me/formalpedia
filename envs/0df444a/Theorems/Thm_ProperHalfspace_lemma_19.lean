-- Prove2me | Theorems.Thm_ProperHalfspace_lemma_19
-- name    : ProperHalfspace.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:30.506762+00:00
-- url     : https://prove2.me/theorems/a91b6d9a-5b75-4acc-b99e-75c560037195
-- title:
--   Lemma 19 — the empirical head and top eigenspace
-- statement:
--   Fix $\rho,\alpha\in(0,1)$, $\lambda>0$ and $f:\{\pm1\}^n\to[-1,1]$, and put $t=(1-\rho)\alpha$. Suppose $\hat M\succeq0$, $\mathrm{Tr}(\hat M)\le1$, and
--   $$\|\hat M-M_\rho(f)\|_{\mathrm{op}}\le\lambda/2,\qquad\max_i|\hat M_{ii}-M_\rho(f)_{ii}|\le t/2.$$
--   Define $\hat H=\{i:\hat M_{ii}>t/2\}$, $\hat T=\hat H^c$ and $\hat E(\hat H)=\mathrm{Eigen}_{\lambda/2}(\hat M[\hat T,\hat T])$. Then:
--
--   1. $|\hat H|\le2/t$;
--   2. $\dim\hat E(\hat H)\le2/\lambda$;
--   3. $\hat H$ satisfies (8);
--   4. every unit $v\in\hat E(\hat H)^\perp$ satisfies $v^\top M_{\mathrm{tail}}(\hat H)v\le\lambda$;
--   5. every unit $u\in\hat E(\hat H)$ satisfies $\|u\|_\infty\le\sqrt{t/\lambda}$.
--
--   An accurate estimate therefore produces a head and a subspace with the properties Theorem 18 requires.
--
--   Differences from the source:
--   - generalization: the target f of §4, whose type the page leaves implicit (Boolean in Theorem 1) → f : {±1}ⁿ → [−1,1]; reason: Remark 21, p.30: the structural and matrix-estimation arguments use only that f is bounded by 1; Boolean f is the special case
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Lemma 19, p.25; standing ρ ∈ (0,1) of §4.1, p.21

import Mathlib
import Definitions.Def_ProperHalfspace_TopEigenspace
import Definitions.Def_ProperHalfspace_HeadTail

namespace ProperHalfspace

/-- Lemma 19, p.25. De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026). Put `t = (1−ρ)α`, and suppose `M̂ ⪰ 0`, `Tr M̂ ≤ 1`,
`‖M̂ − M_ρ(f)‖_op ≤ λ/2` and `maxᵢ |M̂_ii − M_ρ(f)_ii| ≤ t/2`. With `Ĥ = {i : M̂_ii > t/2}`, `T̂ = Ĥᶜ` and `Ê = Eigen_{λ/2}(M̂[T̂, T̂])`: `|Ĥ| ≤ 2/t`,
`dim Ê ≤ 2/λ`, `Ĥ` satisfies (8), every unit `v ∈ Ê⊥` has `v^⊤ M_tail(Ĥ) v ≤ λ`, and every unit `u ∈ Ê` has `‖u‖_∞ ≤ √(t/λ)`.

**Formalization Note.** `Ĥ` and `Ê` are constructed from `M̂`, as on the page. `ρ ∈ (0, 1)` is the standing assumption of §4.1, p.21,
and `α ∈ (0, 1)`, `λ > 0` come from (7) and Definition 14. -/
theorem lemma_19 {n : ℕ} (f : Cube n → ℝ) (hf : IsBoundedOne f) (ρ α lamE : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lamE) (Mhat : Matrix (Fin n) (Fin n) ℝ)
    (hpsd : Mhat.PosSemidef) (htr : Mhat.trace ≤ 1)
    (hop : opNorm (Mhat - pcaMatrix ρ f) ≤ lamE / 2)
    (hdiag : ∀ i, |Mhat i i - pcaMatrix ρ f i i| ≤ (1 - ρ) * α / 2)
    (Hhat : Finset (Fin n)) (hHhat : Hhat = Finset.univ.filter fun i => (1 - ρ) * α / 2 < Mhat i i) :
    let Ehat := topEigenspace (Mhat.submatrix (Subtype.val : {i // i ∉ Hhat} → Fin n) Subtype.val) (lamE / 2)
    (Hhat.card : ℝ) ≤ 2 / ((1 - ρ) * α) ∧
    (Module.finrank ℝ Ehat : ℝ) ≤ 2 / lamE ∧
    HeadCond ρ α f Hhat ∧
    (∀ v ∈ Ehatᗮ, ‖v‖ = 1 → quadForm (tailMatrix ρ f Hhat) v ≤ lamE) ∧
    (∀ u ∈ Ehat, ‖u‖ = 1 → ∀ i, |u i| ≤ Real.sqrt ((1 - ρ) * α / lamE)) := by sorry

end ProperHalfspace
