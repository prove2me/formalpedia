-- Prove2me | Theorems.Thm_SymThrWires_Main_lemma_4_3
-- name    : SymThrWires.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:17:11.079979+00:00
-- url     : https://prove2.me/theorems/7720eb09-bfdc-42b3-8f69-0730838d9e58
-- title:
--   Lemma 4.3 — a trace-potential bound gives average normalized operator-norm error ≤ η
-- statement:
--   Let $Z$ be a nonempty finite set of columns, $m\ge1$, $0<\eta\le1$, and $Q\ge 1024\,N m\,\eta^{-2}(4N^2I)^{1/m}$. If real $N\times N$ matrices $E_t(z)$, $z\in Z$, $t\in\{1,\dots,I\}$, satisfy
--   $$\sum_{z\in Z}\sum_{t}\mathrm{tr}\,H(E_t(z))^{2m}\le|Z|\,I\,4N^2\Big((4QN^3)^m m!+(8N^2/3)^{2m}(2m)!\Big),$$
--   then
--   $$\frac1{|Z|}\sum_{z\in Z}\max_t\frac{\|E_t(z)\|}{QN}\le\eta ,$$
--   where $\|\cdot\|$ is the operator norm.
--
--   It turns the potential bound that the sampler certifies into the average estimation error over columns.
--
--   **Formalization Note.** The operator norm is the published `HighDimProb.QuadraticForms.opNorm` (the norm of the induced map on Euclidean space). The maximum over $t$ is a supremum in `NNReal` of the nonnegative norms, which is the maximum (and $0$ when $I=0$).
--
--   Differences from the source:
--   - encoding: matrices E_t(z), t ≤ I, and max_t → E : α → Fin I → Matrix, max as `Finset.univ.sup` in NNReal; reason: t ranges over the I matrices of the potential (I = 2|Θ| in use); the sup of nonnegative reals over a finite set is their maximum
--   - encoding: Z a nonempty finite set of columns → Z : Finset α for an arbitrary type α, with Z.Nonempty; reason: columns are only an index set
-- source:
--   Dev Nag, Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits, STOC 2027 submission, Zenodo doi:10.5281/zenodo.23847026 (sha256 02f54f02…), p. 16, Lemma 4.3

import Mathlib
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_SymThrWires_Main_Sampling

namespace SymThrWires.Main

/-- **Lemma 4.3** (From a potential bound to an average error, p. 16). Let `Z` be a nonempty finite
set of columns, `m ≥ 1`, `0 < η ≤ 1`, and `Q ≥ 1024 N m η^{−2} (4N²I)^{1/m}`. If real `N × N`
matrices `E_t(z)`, `z ∈ Z`, `t ∈ [I]`, satisfy
`Σ_{z∈Z} Σ_t tr H(E_t(z))^{2m} ≤ |Z| I 4N²((4QN³)^m m! + (8N²/3)^{2m}(2m)!)`, then
`|Z|^{−1} Σ_{z∈Z} max_t ‖E_t(z)‖ / (QN) ≤ η`, `‖·‖` the operator norm. -/
theorem lemma_4_3 {α : Type} (N Q I m : ℕ) (Z : Finset α) (hZ : Z.Nonempty) (hm : 1 ≤ m)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hQ : 1024 * (N : ℝ) * (m : ℝ) * η⁻¹ ^ 2 * (4 * (N : ℝ) ^ 2 * (I : ℝ)) ^ ((1 : ℝ) / m) ≤ (Q : ℝ))
    (E : α → Fin I → Matrix (Fin N) (Fin N) ℝ)
    (hpot : ∑ z ∈ Z, ∑ t : Fin I, Matrix.trace (dilation (E z t) ^ (2 * m)) ≤
      (Z.card : ℝ) * (I : ℝ) * (4 * (N : ℝ) ^ 2 * ((4 * (Q : ℝ) * (N : ℝ) ^ 3) ^ m * (m.factorial : ℝ) +
        (8 * (N : ℝ) ^ 2 / 3) ^ (2 * m) * ((2 * m).factorial : ℝ)))) :
    (Z.card : ℝ)⁻¹ * ∑ z ∈ Z,
        ((Finset.univ.sup (fun t : Fin I =>
            Real.toNNReal (HighDimProb.QuadraticForms.opNorm (E z t))) : NNReal) : ℝ) /
          ((Q : ℝ) * (N : ℝ)) ≤ η := by sorry

end SymThrWires.Main
