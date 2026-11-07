-- Prove2me | Theorems.Thm_PrettyGoodShadow_lemma_4_8
-- name    : PrettyGoodShadow.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:26:34.492211+00:00
-- url     : https://prove2.me/theorems/ddd5c749-d21e-451d-9922-5f3f1c30e955
-- title:
--   Lemma 4.8 — $D(B_x^{\otimes k}\|B^{(k)}_{\hat x}(p,n))\le\Delta_x(p,n)$
-- statement:
--   Fix a prior $p$, a label $x\in\operatorname{supp}(p)$ and integers $n,k\ge1$, and let $0\preceq A\preceq I$. Apply the integral pretty good measurement associated with $\{p_y,\rho_y^{\otimes n}\}$ to $n$ copies of $\rho_x$, and let $\hat x$ be its outcome. Then
--
--   $$
--   D\big(B_x^{\otimes k}\,\big\|\,B^{(k)}_{\hat x}(p,n)\big)\le\Delta_x(p,n).
--   $$
--
--   This is the only step of the proof of Lemma 4.3 that depends on the output of the algorithm.
--
--   **Formalization Note** The inequality is in the extended reals with $\Delta_x$ coerced, so it also says that the left side is finite.
--
--   Differences from the source:
--   - reading: p.21 has one prior p throughout; the restatement on p.23 prints prior q on the left and Δ_x(p, n) on the right, while its proof ends at Δ_q(x, n) → the p.21 form, with one prior; reason: the mixed form is a typo: the proof ends with one prior, and the mixed form failed in 82 of 200 random instances (missions/planning_sim.py)
--   - encoding: y ∈ X in the ensemble → y ∈ L, the label type; reason: X is a typo for the label set L
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Lemma 4.8, p.21 (restated p.23)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodShadow_pgmEffect
import Definitions.Def_PrettyGoodShadow_Delta

namespace PrettyGoodShadow

open ShadowTomography.UpperBound (tensorPow)
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

/-- **Lemma 4.8** (arXiv:2610.06781, sha256 bd055b7d…, p.21). Fix a prior `p`, a label `x ∈ supp(p)` and integers
`n, k ≥ 1`. Apply the integral PGM of `{p_y, ρ_y^{⊗n}}` to `n` copies of `ρ_x`, with outcome `x̂`. Then
`D(B_x^{⊗k} ∥ B^{(k)}_x̂(p, n)) ≤ Δ_x(p, n)`.

**Formalization Note** The p.21 form, with one prior on both sides. The restatement on p.23 prints prior `q` on the
left and `Δ_x(p, n)` on the right, while its proof ends at `Δ_q(x, n)`. The inequality is in `EReal`, with `Delta`
coerced, so it also says that the left side is finite. `0 ⪯ A ⪯ I` is the standing assumption of §4.1, p.19. -/
theorem lemma_4_8 {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (ρ : L → Matrix d d ℂ)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (A : Matrix d d ℂ) (hA : QAlgorithms.IsEffect A)
    (p : L → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (x : L) (hx : 0 < p x)
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    relativeEntropy (tensorPow (bern (obs A (ρ x))) k) (bernMix A ρ (pgmLaw p ρ n x) k) ≤
      ((Delta p ρ A n k x : ℝ) : EReal) := by sorry

end PrettyGoodShadow
