-- Prove2me | Theorems.Thm_SampleRemoval_rounding_step
-- name    : SampleRemoval.rounding_step
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T05:13:35.973691+00:00
-- url     : https://prove2.me/theorems/4422fd30-e8d4-4322-abef-0f108f16e341
-- title:
--   Theorem 3.3, proof (Rounding) — round fractional coordinates to an indicator in $\mathcal W$
-- statement:
--   Assume the design is in general position, and let $\mathcal W$ be the feasible set of a pair $(e,\theta)$. Let $u\in\mathcal W$ and let $I=\{i:u_i=1\}$ satisfy $|I|\ge d$. Then there is a set $S$ with
--
--   $$
--   I\subseteq S\subseteq\mathrm{supp}(u)\qquad\text{and}\qquad \mathbf 1_S\in\mathcal W .
--   $$
--
--   In the paper the fractional coordinates of $u$ are processed one at a time; by Lemma 3.1 each can be moved to an endpoint $0$ or $1$ while staying feasible, and the Gram matrix stays positive definite because $u\ge\mathbf 1_I$. Applied to the sparse weighting of Lemma 3.2 this gives the indicator $\mathbf 1_S$ of Theorem 3.3 with $n-|S|\le n-|I|$.
--
--   Differences from the source:
--
--   - encoding: observations (x_i, y_i) ∈ ℝᵈ × ℝ indexed by i ∈ [n] → x : Fin n → Fin d → ℝ, y : Fin n → ℝ, paper index i = Lean index i − 1; reason: Lean convention; same instances
--   - reading: the procedure "process the elements t ∈ J one at a time … At the end u = 1_S with S ⊇ I and 1_S ∈ 𝒲" → existence of S with I ⊆ S and 1_S ∈ 𝒲; reason: the proof paragraph is stated by its outcome; the step-by-step invariant is the proof of that outcome
--   - generalization: u starts at w′ of Lemma 3.2, with |J| ≤ d fractional coordinates and |I| > d → any u ∈ 𝒲 with |I| ≥ d, any number of fractional coordinates; reason: each step uses only Σ_{i∈I} x_i x_i⊤ ≻ 0, which GP gives for |I| ≥ d (Remark 3.5: "I spans ℝᵈ"); w′ satisfies the hypotheses
--   - generalization: S ⊇ I → I ⊆ S ⊆ supp(u); reason: the procedure changes only coordinates in J, so S ⊆ I ∪ J = supp(u); dropping the extra conjunct gives the source's conclusion
--   - generalization: (e, θ) is a target, ⟨e, β([n])⟩ > θ (§2, Audits) → (e, θ) ∈ ℝᵈ × ℝ arbitrary; reason: the statement and its proof do not use the target condition; taking a target specializes to the source's claim
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Theorem 3.3, proof paragraph "Rounding.", p.5 (PDF p.7)

import Mathlib
import Definitions.Def_SampleRemoval_ind
import Definitions.Def_SampleRemoval_feasible
import Definitions.Def_SampleRemoval_GeneralPosition

set_option autoImplicit false

namespace SampleRemoval

/-- **Theorem 3.3, proof paragraph "Rounding."** (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), p.5). Process the fractional coordinates
`t ∈ J` one at a time, maintaining `u ∈ 𝒲` that equals 1 on `I = {i : uᵢ = 1}` and lies in
`{0, 1}` outside the unprocessed part of `J`; by Lemma 3.1 each step can move `uₜ` to an
endpoint `a* ∈ {0, 1}` and stay in `𝒲`, since `G(u) ⪰ Σ_{i∈I} xᵢxᵢ⊤ ≻ 0` by GP. "At the end
u = 1_S with S ⊇ I and 1_S ∈ 𝒲."

Stated as its outcome: under GP, if `u ∈ 𝒲` has at least `d` coordinates equal to `1`, there
is `S` with `{i : uᵢ = 1} ⊆ S ⊆ {i : uᵢ ≠ 0}` and `1_S ∈ 𝒲`.

**Formalization Note** The paper applies the step to the sparse `w′` of Lemma 3.2, with
`|J| ≤ d` and `|I| > d`; the statement allows any `u ∈ 𝒲` (any number of fractional
coordinates) and needs only `|I| ≥ d` (Remark 3.5: "I spans ℝᵈ"). The conclusion
`S ⊆ supp(u)` records that coordinates outside `J` are not changed. `(e, θ)` is arbitrary. -/
theorem rounding_step {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ)
    (θ : ℝ) (hGP : GeneralPosition x) (u : Fin n → ℝ) (hu : u ∈ feasible x y e θ)
    (hI : d ≤ (Finset.univ.filter (fun i => u i = 1)).card) :
    ∃ S : Finset (Fin n), Finset.univ.filter (fun i => u i = 1) ⊆ S ∧
      S ⊆ Finset.univ.filter (fun i => u i ≠ 0) ∧ ind S ∈ feasible x y e θ := by sorry

end SampleRemoval
